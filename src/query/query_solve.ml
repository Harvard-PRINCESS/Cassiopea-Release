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
open Solver

(* methods for querying solvers *)

(* keep a solver for fire-and-forget queries *)
let esolver : solver option ref = ref None
let get_esolver () =
  match !esolver with
  | Some solv -> solv
  | None ->
    let solv = solver_create !settings.cex_solver in
    esolver := Some solv; solv

(* find a model that satisfies the given assertion *)
(* uses fire-and-forget solver *)
let esolve asserts =
  let solv = get_esolver () in
  solver_assert solv asserts;
  solver_push solv;
  let sol = solver_check solv in
  solver_clear solv; sol

(* type for synthesis problems *)
type ea_term = {
  meta : vars;      (* implicitly forall-quantified, duplicated per-query *)
  inputs : vars;    (* forall-quantified variables *)
  controls : vars;  (* exists-quantified variables *)
  axioms : bool sym_value;  (* assertions over metavariables *)
  assumes : bool sym_value; (* precondition *)
  asserts : bool sym_value; (* postcondition *)
}

(* add a list of counterexamples to candidate generation solver *)
let easolve_add syn_solv cexs (t : ea_term) =
  let add_cex cex =
    let cond = log_and t.asserts t.axioms |> subst cex in
    let model = model_refresh t.meta in
    solver_assert syn_solv (subst model cond);
    solver_push syn_solv;
  in
  List.iter add_cex cexs

(* try to find a correct program *)
let easolve_guess syn_solv (t : ea_term) =
  let start_time = Unix.gettimeofday () in

  let cand = solver_check syn_solv in

  print_log "Guessing Time: %fs\n" (Unix.gettimeofday () -. start_time);
  flush_log ();

  match cand with
  | None -> None
  | Some m ->
    if !settings.dump_solver then begin
      print_log "return-model: %s\n" (string_of_model m);
      flush_log ()
    end;

    let m = m
      |> model_complete t.controls
      |> model_project t.controls
    in

    if !settings.dump_solver then begin
      print_log "complete-model: %s\n" (string_of_model m);
      flush_log ()
    end;
    Some m

(* try to find up to n counterexamples *)
let easolve_check n cand (t : ea_term) =
  let start_time = Unix.gettimeofday () in

  (* one of the two active solvers. this is the checking solver *)
  let cex_solv = solver_create !settings.cex_solver in
  solver_assert cex_solv (subst cand t.axioms);
  solver_assert cex_solv t.assumes;

  (* get up to n distinct counterexamples *)
  let rec get_n cexs n p =
    if n <= 0 then
      cexs
    else begin
      solver_assert cex_solv p;
      solver_push cex_solv;
      let cexs =
        match solver_check cex_solv with
        | Some m ->
          get_n (m :: cexs) (n - 1) (log_not (assert_of_model m))
        | None ->
          cexs
      in
      cexs
    end
  in

  let cexs = get_n [] n (log_not (subst cand t.asserts)) in
  solver_close cex_solv;

  print_log "Checking Time: %fs\n" (Unix.gettimeofday () -. start_time);
  flush_log ();

  let cexs = cexs
    |> List.map (model_complete t.inputs)
    |> List.map (model_project t.inputs)
  in

  if !settings.dump_solver then begin
    print_log "CEX: %s\n"
      (cexs
      |> List.map string_of_model
      |> String.concat "\n");
    flush_log ()
  end;

  cexs

(* find a model for the controls that satisfies the given assertions under all
   assignments to the input variables that satisfy the given assumptions *)
let easolve model_printer cexs (t : ea_term) =
  (* check variable coverage *)
  let vars_free =
    (vars_of_sym_value t.axioms) |> vars_union
    (vars_of_sym_value t.assumes) |> vars_union
    (vars_of_sym_value t.asserts)
  in
  let vars_bound =
    t.meta |> vars_union t.inputs |> vars_union t.controls
  in
  let vars_unbound = vars_diff vars_free vars_bound in
  (if not (vars_is_empty vars_unbound) then
    failwith "easolve: found unbound vars!");

  (* one of the two active solvers. this is the guessing solver *)
  let syn_solv = solver_create !settings.syn_solver in

  (* add starting counterexamples *)
  easolve_add syn_solv cexs t;

  (* iteration count *)
  let iter_count = ref 0 in

  (* run one round of cegis *)
  (* cexs is current list of counterexamples *)
  let rec do_cegis cexlist candlist =
    iter_count := !iter_count + 1;

    print_log "Iter %s Guessing...\t" (string_of_int !iter_count);
    flush_log ();

    match easolve_guess syn_solv t with
    (* no candidate found: abort *)
    | None -> (None, (cexlist, candlist))
    (* candidate found: find counterexamples *)
    | Some cand ->
      model_printer cand;

      print_log "Iter %s Checking...\t" (string_of_int !iter_count);
      flush_log ();

      match easolve_check 1 cand t with
      (* no counterexamples found: finish *)
      | [] -> (Some cand, (cexlist, candlist))
      (* counterexamples found: add, and find another candidate *)
      | cexs ->
        if !settings.dump_solver then begin
          print_log "COUNTEREXAMPLE: \n%s\n"
            (List.fold_left (fun s v -> s^(string_of_model v)^"\n") "" cexs);
          flush_log ()
        end;
        easolve_add syn_solv cexs t;
        do_cegis (cexs @ cexlist) (cand :: candlist)
  in

  let sol = do_cegis cexs [] in
  solver_close syn_solv;
  sol

(* BELOW IS ONLY USED FOR COUNTEREXAMPLE BUCKETS *)
(* find a model for the controls that satisfies the given assertions under all
   assignments to the input variables that satisfy the given assumptions
   using cegis counterexample bucket method *)
let easolve_bucket model_printer (t : ea_term) =
  let _ = model_printer, t in
  failwith "buckets not currently supported"
  (* if !settings.debugging then begin
    print_log "INPUTS: \n%s\n(INPUTS end)\n" (string_of_vars t.inputs);
    print_log "CONTROLS: \n%s\n(CONTROLS end)\n" (string_of_vars t.controls);
    flush_log ()
  end;

  (* variable sanity checks *)
  if not (vars_is_empty (vars_diff (vars_of_sym_value t.assumes) t.inputs)) then
    failwith "non-input vars in assumes!"
  else begin
    let vars =
      (vars_of_sym_value t.assumes) |> vars_union
      (vars_of_sym_value t.asserts) |> vars_union
      (vars_of_sym_value t.axioms)
    in
    let manifest =
      t.inputs |> vars_union t.controls |> vars_union t.meta
    in
    if not (vars_is_empty (vars_diff vars manifest)) then
      failwith "vars in expressions not in varlists!"
  end;

  let iter_count = ref 0 in
  let cndbck = ref IM.empty in
  let cndbckcnt = ref 0 in

  (* try to find a a correct program *)
  let guess cexls (* IntMap of valid counterexamples *) =
    let syn_solv = solver_create Z3 in
    let cexs = IM.bindings cexls in

    print_log "Iter %s Guessing...\t" (string_of_int !iter_count);
    flush_log ();

    let start_time = Unix.gettimeofday () in

    let add_cex (_, cex) =
      (* refresh metavariables *)
      let cond = log_and t.axioms t.asserts |> subst cex in
      let model = t.controls (* expect no input vars remain *)
        |> vars_diff (vars_of_sym_value cond)
        |> model_refresh
      in
      solver_assert syn_solv (subst model cond);
      solver_push syn_solv;

      if !settings.debugging then begin
        print_log "REFRESH-MODEL(guess): \n%s\n(REFRESH-MODEL-guess end)\n"
          (string_of_model model);
        flush_log ()
      end;
    in

    let cand =
      if cexs = [] then
        (solver_assert syn_solv (log_and t.axioms t.asserts);
        solver_push syn_solv;
        solver_check syn_solv)
      else
        (List.iter add_cex cexs; solver_check syn_solv)
    in

    print_log "Guessing Time: %fs\n" (Unix.gettimeofday () -. start_time);
    flush_log ();

    solver_close syn_solv;
    match cand with
    | Some m -> Some (m
      |> model_complete t.controls
      |> model_project t.controls)
    | None -> None
  in

  let check cand (* candidate to validate *) =
    print_log "Iter %s Multi-Checking...\t"
      (string_of_int !iter_count);
    flush_log ();

    let start_time = Unix.gettimeofday () in

    let check_bucket (cands: model list) =
      let cex_solv = solver_create Z3 in
      solver_assert cex_solv t.assumes;

      let one_cand cand =
        (* refresh metavariables *)
        let cond = log_not (log_and t.asserts t.axioms) |> subst cand in
        let model = t.inputs (* expect no control vars remain *)
          |> vars_diff (vars_of_sym_value cond)
          |> model_refresh
        in

        solver_assert cex_solv (subst model cond);
        solver_push cex_solv;

        if !settings.debugging then begin
          print_log "REFRESH-MODEL(check): \n%s\n(REFRESH-MODEL-guess end)\n"
            (string_of_model model);
          flush_log ()
        end;
      in

      List.iter one_cand cands;
      (* XXX here previously asserted constraints without subst'ing cand *)
      (* is that really necessary?! *)
      let cex = solver_check cex_solv in
      solver_close cex_solv;

      match cex with
      | Some cex -> [cex
        |> model_complete t.inputs
        |> model_project t.inputs]
      | None -> []
    in

    let cexbck = IM.map check_bucket (!cndbck) in
    let valid_cexbck = IM.filter (fun _ v -> match v with | [] -> false | _ -> true) cexbck in
    match IM.min_binding_opt valid_cexbck with
    | Some (k, v) ->
      (* add current cand to the existing bucket *)
      let curbck = IM.find k (!cndbck) in
      cndbck := IM.add k (curbck @ [cand]) (!cndbck);
      print_log "Multi-Checking for old bucket %s in %s, Time: %fs\n"
        (string_of_int k)
        (string_of_int !cndbckcnt)
        (Unix.gettimeofday () -. start_time);
      flush_log ();
      (k, v)
    | None ->
      (* current buckets failed to generate a cex *)
      let cex_solv = solver_create Z3 in
      solver_assert cex_solv t.assumes;
      solver_assert cex_solv (log_not (log_and t.asserts t.axioms) |> subst cand);
      solver_push cex_solv;
      let cexs = solver_check cex_solv in
      solver_close cex_solv;
      begin match cexs with
      | Some cexs ->
        cndbckcnt := !cndbckcnt + 1; (* new bucket *)
        cndbck := IM.add (!cndbckcnt) [cand] (!cndbck);
        let ccex = [(cexs |> model_complete t.inputs |> model_project t.inputs)] in
        print_log "Multi-Checking for new bucket %s in %s, Time: %fs\n"
          (string_of_int !cndbckcnt)
          (string_of_int !cndbckcnt)
          (Unix.gettimeofday () -. start_time);
        flush_log ();
        (!cndbckcnt, ccex)
      | None -> (0, [])
      end
  in

  (* run one round of cegis with given counterexample lists *)
  (* given:
     - next list of counterexamples to use,
     - list of already-seen counterexamples *)
  let rec cegis (cexs: model IM.t) =
    iter_count := !iter_count + 1;
    match guess cexs with
    (* no candidate found: abort *)
    | None -> (None, cexs)
    (* candidate found: find counterexamples *)
    | Some cand ->
      model_printer cand;
      match check cand with
      (* no counterexamples found: finish *)
      | (_, []) ->
        (Some cand, cexs)
      (* counterexamples found: find candidate *)
      | (i, [cex]) ->
        let cexs = IM.add i cex cexs in
        if !settings.dump_solver then begin
          print_log "CEX: %s\n" (string_of_model cex);
          flush_log ()
        end;
        if !settings.synth_verbose then begin
          print_log "CEX has %s buckets\n" (string_of_int (IM.cardinal cexs));
          flush_log ()
        end;
        cegis cexs
      | _ ->
        failwith ("single check generated multiple cex!")
  in
  match (cegis IM.empty) with
  (* no solution found; output counterexamples *)
  | (None, cexs) -> (None, List.map snd (IM.bindings cexs))
  (* solution found; output a program *)
  | (Some model, cexs) -> (Some model, List.map snd (IM.bindings cexs))
*)
