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
open Query_hammer

(* representation of a separation-logic-like predicate over a config *)
(* spatial fragment can be read as a set of equality assertions of the form:
   - *reg == something
   - *[mem, loc] == something *)
type spred = {
  (* pure fragment *)
  pure : bool sym_value;

  (* spatial fragment *)
  reg : (word sym_value * int) SM.t;
  mem : (int * int * word sym_value BM.t) SM.t;
}

let string_of_spred pred =
  "PURE: "^(string_of_sym_value pred.pure)^"\n"^
  "REG:\n======\n"^(string_of_reg pred.reg)^"\n"^
  "MEM:\n======\n"^(string_of_mem pred.mem)

(* variables in a predicate *)
let vars_of_pred pred =
  (vars_of_sym_value pred.pure)
  |> vars_union (vars_of_reg pred.reg)
  |> vars_union (vars_of_mem pred.mem)

let subst_pred model pred =
  let tbl = mk_memo_tmap () in
  { pure = subst' tbl model pred.pure;
    reg = subst_reg' tbl model pred.reg;
    mem = subst_mem' tbl model pred.mem; }

(* does the pred imply that a given condition holds over the state? *)
(* variables in the condition should be from the state *)
let pred_implies (pred : spred) (v : bool sym_value) =
  let pred_vars = vars_of_pred pred in
  let cond_vars = vars_of_sym_value v in
  (if not (vars_is_empty (vars_diff cond_vars pred_vars)) then
    failwith "pred_implies: condition contains variables missing from state!");

  let term = log_and pred.pure (log_not v) in
  match esolve term with
  | None -> true
  | Some _ -> false

(* evaluate condition over config *)
(* generate seplogic predicate with condition as pure *)
let eval_pred e (conf : config) : spred =
  let pure =
    match eval_expr e conf with
    | Ok (ValBool b, ctx) ->
      log_and b (ctx_to_bool ctx)
    | Ok _ ->
      failwith "eval_bool: condition evaluated to non-boolean"
    | Error (pos, s) ->
      failwith ("eval_bool: condition evaluation failed\n"^
                "error: "^(Pos.string_of pos)^": "^s)
  in
  { pure = pure;
    reg = conf.reg;
    mem = conf.mem; }

(* coerce general words to vecs when possible *)
(* NOTE this is quite aggressive; we won't support a maybe-pointer precond *)
let coerce_pred pred =
  let vars = vars_of_sym_value pred.pure in
  let do_coerce b v =
    if !settings.weak_coerce then
      vars_is_empty (vars_inter vars (vars_of_sym_value v))
    else
      not (pred_implies pred (mk_unop LogNot b))
  in

  (* adds a substitution that coerces a word to a vec *)
  (* assumes word is canonicalized, i.e. has been run through simpl *)
  let coerce_word (w : word sym_value) model =
    match w.node with
    | SymIte (b, v, _) ->
      begin match (b.node, v.node) with
      | (SymBool i, SymVal (IsWord _, BitVec _))
        when do_coerce b w ->
        model_add_bool i (mk_bool true) model
      | _ -> model
      end
    | _ -> model
  in

  let coerce_regs _ (v, _) model =
    coerce_word v model
  in
  let coerce_mems _ (_, _, m) model =
    BM.fold (fun _ -> coerce_word) m model
  in
  let model = model_empty
    |> SM.fold coerce_regs pred.reg
    |> SM.fold coerce_mems pred.mem
  in

  subst_pred model pred

(* hammer a predicate with given pure cond *)
let hammer_pred vars pure pred =
  let memo = mk_memo_tmap () in
  let hammer_reg (v, l) =
    (hammer' memo vars pure v, l)
  in
  let hammer_mem (l, n, m) =
    (l, n, BM.map (hammer' memo vars pure) m)
  in
  { pure = hammer' memo vars pure pred.pure;
    reg = SM.map hammer_reg pred.reg;
    mem = SM.map hammer_mem pred.mem; }

(* frame irrelevant heap elements out of a predicate *)
(* an element is irrelevant when:
   1. it contains no vars in the var set, AND
   2. it is NOT in the may-modify set *)
let frame_pred vars mod_regs mod_mems (pred : spred) : spred =
  let modifiable_reg i =
    SS.mem i mod_regs
  in
  let modifiable_mem i o =
    let o = Bits.to_int o in
    let check (i', o') = (i = i') && (o = o') in
    List.exists check mod_mems
  in

  let is_relevant v =
    not (vars_is_empty (vars_inter vars (vars_of_sym_value v)))
  in
  let frame_reg i (v, l) regs =
    if is_relevant v || modifiable_reg i then
      SM.add i (v, l) regs
    else regs
  in
  let frame_mem i (l, n, m) mems =
    let frame_region o v region =
      if is_relevant v || modifiable_mem i o then
        BM.add o v region
      else region
    in
    let m = BM.fold frame_region m BM.empty in
    if BM.is_empty m then
      mems
    else
      SM.add i (l, n, m) mems
  in
  { pred with
    reg = SM.fold frame_reg pred.reg SM.empty;
    mem = SM.fold frame_mem pred.mem SM.empty; }

(* expand the spatial fragment footprint of pred to full frame *)
(* new entries in pred are equal to those in frame, asserting equality *)
let unframe_pred frame_reg frame_mem (pred : spred) : spred =
  (* add missing registers *)
  let add_reg i (v, l) regs =
    match SM.find_opt i regs with
    | None -> SM.add i (v, l) regs
    | Some _ -> regs
  in
  (* add missing memory locations *)
  let add_mem i (l, n, m) mems =
    let add_region o v region =
      match BM.find_opt o region with
      | None -> BM.add o v region
      | Some _ -> region
    in
    let region =
      match SM.find_opt i mems with
      | None -> BM.empty
      | Some (l', n', region) ->
        if l <> l' || n <> n' then
          failwith ("unframe_pred: type mismatch in region "^i)
        else region
    in
    SM.add i (l, n, BM.fold add_region m region) mems
  in
  { pred with
    reg = SM.fold add_reg frame_reg pred.reg;
    mem = SM.fold add_mem frame_mem pred.mem; }

(* convert pred to full config *)
(* elements missing from the pred will specify arbitrary vecs *)
let config_of_pred (c : casp) (pred : spred) : config =
  (* create full frame for machine description footprint *)
  let mk_reg l = (next_sym_word_vec l, l) in
  let mk_mem (l, n, r, _) =
    let add_entry region o =
      let o = Bits.of_int r (o * (l / 8)) in
      BM.add o (next_sym_word_vec l) region
    in
    (l, n, List.fold_left add_entry BM.empty (range 0 n))
  in
  let full_reg = SM.map mk_reg c.regs in
  let full_mem = SM.map mk_mem c.mems in

  let pred = unframe_pred full_reg full_mem pred in

  let env = eval_env c in
  { c = c;
    top = env;
    env = env;
    reg = pred.reg;
    mem = pred.mem;
    ctx = ctx_init;
    jmp = mk_int BI.zero_big_int; }

(* create DAG containing every pure + spatial predicate in DAG *)
let dag_of_pred (pred : spred) =
  let add_reg _ (v, _) dag = dag_add v dag in
  let add_mem _ (_, _, m) dag =
    let add_region _ v dag = dag_add v dag in
    BM.fold add_region m dag
  in
  dag_add pred.pure dag_empty
  |> SM.fold add_reg pred.reg
  |> SM.fold add_mem pred.mem

let apply_reg f (pred : spred) (conf : config) =
  let apply_one i (v, _) =
    match SM.find_opt i conf.reg with
    | Some (v', _) -> f i v v'
    | None -> failwith ("apply_reg: register "^i^" missing from config!")
  in
  let apps = SM.mapi apply_one pred.reg in
  SM.fold (fun _ -> log_and) apps (mk_bool true)

let apply_mem f (pred : spred) (conf : config) =
  let apply_region i (_, _, region) =
    match SM.find_opt i conf.mem with
    | Some (_, _, region') ->
      let apply_one o v =
        match BM.find_opt o region' with
        | Some v' -> f i o v v'
        | None ->
          failwith ("apply_pred: memory region "^i^" missing offset "^
                    (string_of_int (Bits.to_int o))^" from config!")
      in
      let region_eqs = BM.mapi apply_one region in
      BM.fold (fun _ -> log_and) region_eqs (mk_bool true)
    | None ->
      failwith ("apply_pred: memory region "^i^" missing from config!")
  in
  let apps = SM.mapi apply_region pred.mem in
  SM.fold (fun _ -> log_and) apps (mk_bool true)

(* convert predicate to boolean assertion *)
let apply_pred (pred : spred) (conf : config) =
  let reg_assert = apply_reg (fun _ -> eq_word) pred conf in
  let mem_assert = apply_mem (fun _ _ -> eq_word) pred conf in
  pred.pure
  |> log_and (log_and reg_assert mem_assert)
  |> log_and (ctx_to_bool conf.ctx)

(* bind existentials appearing in spatial fragment *)
(* also checks for existential angst: we cannot handle unbound existentials
   in the postcond, since doing so correctly would require solving an
   exists-forall-exists formula *)
(* their appearance here could cause nontermination; check may always succeed *)
let bind_pred evars (pred : spred) (conf : config) =
  (* ANGST CHECK *)
  (* ensure that all evars are bound in spatial postcondition *)
  let reg_vars = vars_of_reg pred.reg in
  let mem_vars = vars_of_mem pred.mem in
  let unbound_evars = vars_diff evars (vars_union reg_vars mem_vars) in
  (if not (vars_is_empty unbound_evars) then
    failwith "ANGST: found unbound existentials in pred!!!");

  (* ANGST CHECK (in bind_reg, bind_mem) *)
  (* ensure that variables in a value are ONLY evars or ONLY avars *)
  (* XXX even this won't catch when postconds are expressions that contain
     only evars but will not fully constrain their values upon equation:
     e.g. exists a b . R1 --> a + b *)
  (* just don't abuse this system *)

  let bind_reg i v1 v2 =
    let vars = vars_of_sym_value v1 in
    let evars' = vars_inter vars evars in
    let avars' = vars_diff vars evars in
    if not (vars_is_empty evars' || vars_is_empty avars') then
      failwith ("ANGST: register "^i^" contains both evars and avars!!!")
    else if not (vars_is_empty evars') then
      eq_word v1 v2
    else
      mk_bool true
  in
  let reg_binder = apply_reg bind_reg pred conf in

  let bind_mem i o v1 v2 =
    let vars = vars_of_sym_value v1 in
    let evars' = vars_inter vars evars in
    let avars' = vars_diff vars evars in
    if not (vars_is_empty evars' || vars_is_empty avars') then
      failwith ("ANGST: memory location at "^
                "["^i^","^(string_of_int (Bits.to_int o))^"] "^
                "contains both evars and avars!!!")
    else if not (vars_is_empty evars') then
      eq_word v1 v2
    else
      mk_bool true
  in
  let mem_binder = apply_mem bind_mem pred conf in

  log_and reg_binder mem_binder
