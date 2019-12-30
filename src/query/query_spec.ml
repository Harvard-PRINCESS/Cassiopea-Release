(****************************************************************************************
BSD License

Copyright (c) 2016-2019, Harvard University
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

    Redistributions of source code must retain the above copyright
    notice, this list of conditions and the following disclaimer.

    Redistributions in binary form must reproduce the above copyright
    notice, this list of conditions and the following disclaimer in
    the documentation and/or other materials provided with the
    distribution.

    Neither the name of the copyright holder nor the names of its
    contributors may be used to endorse or promote products derived
    from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
****************************************************************************************)


open Util
open Symexec

open Query_solve
open Query_pred

(* separation logic-like representation of pre/post specifications *)

(* An sspec is composed of a machine description and separation logic-style
   pre- and post-conditions.
   Parts of the machine state may be omitted from the spec; framing out
   indicates that the value should not be modified by a correct program.
   Variables appearing in the precondition are implicitly universally
   quantified and might be used in the postcondition.
   Variables appearing in the postcondition are implicitly existentially
   quantified.
   To avoid problems with triple quantification, elements of the spatial
   part of the postcondition should be either wholly existential or
   wholly universal.
   Moreover, existential variables should be uniquely instantiable given
   a final state of the program. *)
type sspec = {
  (* machine description *)
  casp : casp;

  (* SL pre- and post-condition *)
  pre  : spred;
  post : spred;
}

let string_of_sspec (spec : sspec) =
  "PRE:\n============\n"^
  (string_of_spred spec.pre)^"\n"^
  "POST:\n============\n"^
  (string_of_spred spec.post)

(* variables in a spec *)
let vars_of_spec spec =
  vars_union (vars_of_pred spec.pre) (vars_of_pred spec.post)

(* variables in a spec, bound in precondition *)
let avars_of_spec spec =
  vars_of_pred spec.pre

(* variables in a spec, bound in postcondition *)
(* these are notionally EXISTENTIALLY QUANTIFIED logical variables *)
(* these need to be handled carefully, or solver calls will die *)
let evars_of_spec spec =
  vars_diff (vars_of_pred spec.post) (vars_of_pred spec.pre)

(* apply substitution to both pre- and post-conditions in a spec *)
let subst_spec model spec =
  { spec with
    pre = subst_pred model spec.pre;
    post = subst_pred model spec.post; }

(* add ghost variables to environment *)
let eval_ghosts lets (conf : config) =
  let add_let (conf: config) (i, _, e) =
    match eval_expr e conf with
    | Ok (v, ctx) ->
      { conf with
        top = SM.add i v conf.top;
        env = SM.add i v conf.env;
        ctx = ctx }
    | Error (pos, s) ->
      failwith ("expr for "^i^" in spec failed\n"^
                "error: "^(Pos.string_of pos)^": "^s)
  in
  List.fold_left add_let conf lets

(* get concrete register modify lists (evaluate name aliases) *)
let eval_frame (conf : config) (frame : SS.t) : SS.t =
  let eval_name i =
    match eval_expr (Pos.none, Atomic (Id i)) conf with
    | Ok (ValLoc (i, _), _) -> lower_loc i
    | Ok _ ->
      failwith ("eval_frame: "^i^" did not evaluate to location")
    | Error (_, s) ->
      failwith ("eval_frame: evaluation failed for "^i^":\n"^s)
  in
  SS.map eval_name frame

(* frame irrelevant heap elements out of spec *)
(* NOTE run before simplifying! *)
let frame_spec mod_regs mod_mems (spec : sspec) : sspec =
  (* get vars mentioned in pure pre or post *)
  let vars_pre = vars_of_sym_value spec.pre.pure in
  let vars_post = vars_of_sym_value spec.post.pure in
  let vars = vars_union vars_pre vars_post in

  (* frame irrelevant elements out of pre/post *)
  { spec with
    pre = frame_pred vars SS.empty [] spec.pre;
    post = frame_pred vars mod_regs mod_mems spec.post; }

(* unframe spec against initial config *)
let unframe_spec (spec : sspec) (init : config) : sspec =
  (* add equality assertions to post *)
  let pre = unframe_pred init.reg init.mem spec.pre in
  let post = unframe_pred pre.reg pre.mem spec.post in
  { spec with pre = pre; post = post; }

(* evaluate a specfile to internal representation *)
let eval_spec (c : casp) (s : spec_file) : sspec =
  (* evaluate precond *)
  let init = next_sym_config c |> eval_ghosts s.lets in
  let pre = eval_pred s.precond init in

  (* project irrelevant pointers; reconstitute ghosts *)
  let pre = coerce_pred pre in
  let init = config_of_pred c pre |> eval_ghosts s.lets in

  (* evaluate postcond *)
  let final =
    { (next_sym_config c) with
      top = init.top; env = init.env }
  in
  let post = eval_pred s.postcond final in

  (* create separation logic pre/post *)
  let spec =
    { casp = c;
      pre = pre;
      post = post; }
  in

  (* frame out irrelevant elements *)
  frame_spec (eval_frame init s.modifyreg) s.modifymem spec

(* apply specification to initial and final configurations *)
(* generates an exists-forall problem *)
let apply_spec spec sp (init : config) (final : config) : ea_term =
  (* unframe spec *)
  let spec = unframe_spec spec init in

  (* get variables *)
  let evars = evars_of_spec spec in
  let avars = avars_of_spec spec in
  let pvars = vars_of_sym_prog sp in

  (* variable sanity check *)
  let final_vars = vars_of_config final in
  (if not (vars_is_empty (vars_diff final_vars (vars_union avars pvars))) then
    failwith "apply_spec: final state contains non-control non-input vars!");

  (* generate synthesis problem *)
  (* TODO use equate to unify instead of bind_pred *)
  let term =
    { meta = evars;
      inputs = avars;
      controls = pvars;

      axioms = bind_pred evars spec.post final;
      assumes = spec.pre.pure;
      asserts = apply_pred spec.post final |> contextual; }
  in

  if !settings.synth_verbose then begin
    print_log "axiom size: %d\n" (size_of_sym_value term.axioms);
    print_log "assume size: %d\n" (size_of_sym_value term.assumes);
    print_log "assert size: %d\n" (size_of_sym_value term.asserts);
  end;

  term
