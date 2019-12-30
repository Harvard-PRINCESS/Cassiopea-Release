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

open Query_pred
open Query_spec

(* unifying equal values in specs *)
(* this thing badly needs a refactor *)

(* get values equal to a boolean v under assumption p via interpolation *)
(* TODO this thing is pretty low-quality *)
let unify_interpolate p v : equality =
  let is_true = context_subst v p in
  let is_false = log_not (context_subst (log_not v) p) in

  (* try to detect common elements between these two *)
  let boolset_of_value (v : bool sym_value) : SBS.t =
    match v.node with
    | SymMultiop (LogAnd, ls, _, _) ->
      List.fold_left (fun s v -> SBS.add v s)
        (SBS.singleton (mk_bool true)) ls
    | _ -> SBS.singleton v
  in

  SBS.inter (boolset_of_value is_true) (boolset_of_value is_false)
  |> SBS.elements
  |> List.fold_left (fun eq v' -> equality_equate v v' eq) (equality_empty ())

(* propose a substitution of constants for the given vars *)
(* also to be provided:
   - constvars are variables to be considered constants
   - ctxmap may provide contexts for vars; can be helpful *)
(* substitution will result in equal expressions under assumption p *)
(* TODO vars and constvars should not overlap! *)
(* TODO produce acyclic models even when they do overlap *)
let unify_vars vars constvars ctxmap (p : bool sym_value) : model =
  (* get set of variables involved in p *)
  (* TODO we only unify for these since nothing else SHOULD be relevant *)
  (* TODO but we should check somehow?! *)
  let vars = vars_inter vars (vars_of_sym_value p) in

  (* get set of values equal to v, for ints and vecs *)
  let get_eqset_num v =
    let ctx =
      match SVM.find_opt (ex_of_sym_value v) ctxmap with
      | Some ctx -> ctx
      | None -> mk_bool true
    in
    context_and p ctx
    |> equality_of_pred
    |> eqset_of_value v
  in

  let get_eqset_bool v =
    let ctx =
      match SVM.find_opt (ex_of_sym_value v) ctxmap with
      | Some ctx -> ctx
      | None -> mk_bool true
    in
    let assume = context_and p ctx in
    equality_of_pred assume
    |> equality_union (unify_interpolate assume v)
    |> eqset_of_value v
  in

  (* gather equality sets on variables *)
  let get_bool_eqset i map = IM.add i (get_eqset_bool (mk_sym_bool i)) map in
  let get_int_eqset i map = IM.add i (get_eqset_num (mk_sym_int i)) map in
  let get_vec_eqset i l map = IM.add i (get_eqset_num (mk_sym_vec i l)) map in

  let bool_eqsets = IS.fold get_bool_eqset vars.bool_set IM.empty in
  let int_eqsets = IS.fold get_int_eqset vars.int_set IM.empty in
  let vec_eqsets = IM.fold get_vec_eqset vars.vec_set IM.empty in

  (* find a constant value in a list of values *)
  (* considering vars in constvars to be constants *)
  let find_const ls =
    let find' found v =
      let vars = vars_of_sym_value v in
      if vars_is_empty (vars_diff vars constvars) then
        begin match found with
        | None -> Some v
        | Some found ->
          (* take this value if it has fewer variables *)
          let sz = vars_size vars in
          let sz' = vars_size (vars_of_sym_value found) in
          if sz < sz' then Some v else Some found
        end
      else found
    in
    List.fold_left find' None ls
  in

  (* find acyclic model *)
  (* TODO use DP to maximize elimination; for now, substitute greedily *)
  let add_subst add v ls model =
    match find_const ls with
    | Some k -> add v k model
    | None -> model
  in

  let model =
    model_empty
    |> IM.fold (add_subst model_add_bool) bool_eqsets
    |> IM.fold (add_subst model_add_int) int_eqsets
    |> IM.fold (add_subst model_add_vec) vec_eqsets
  in

  model

(* simplify using the precondition *)
let unify_pre (spec : sspec) : sspec option =
  let rec do_unify (spec : sspec) : sspec option =
    (* apply context-aware strong simplification to pure conditions *)
    let spec =
      { spec with
        pre = { spec.pre with pure = context_reduce spec.pre.pure };
        post = { spec.post with pure = context_reduce spec.post.pure }; }
    in

    (* hammer the postcond with the pure precond *)
    let spec =
      { spec with
        post = hammer_pred (vars_of_pred spec.pre) spec.pre.pure spec.post; }
    in

    (* find a model from precond, scoped to both pre/post *)
    let ctxmap =
      dag_merge (dag_of_pred spec.pre) (dag_of_pred spec.post)
      |> context_of_dag
    in
    let avars = avars_of_spec spec in
    let model = unify_vars avars vars_empty ctxmap spec.pre.pure in

    if model_is_empty model then
      (* nothing more to unify: return *)
      Some spec
    else
      (* subst and unify again *)
      do_unify (subst_spec model spec)
  in
  do_unify spec

(* simplify using the postcondition *)
let unify_post (spec : sspec) : sspec option =
  let rec do_unify (spec : sspec) : sspec option =
    (* apply context-aware strong simplification to pure conditions *)
    let spec =
      { spec with
        pre = { spec.pre with pure = context_reduce spec.pre.pure };
        post = { spec.post with pure = context_reduce spec.post.pure }; }
    in

    (* hammer the postcond with the pure precond *)
    let spec =
      { spec with
        post = hammer_pred (vars_of_pred spec.pre) spec.pre.pure spec.post; }
    in

    (* find a model from postcond, scoped to postcond *)
    let ctxmap = dag_of_pred spec.post |> context_of_dag in
    let evars = evars_of_spec spec in
    let avars = avars_of_spec spec in
    let model = unify_vars evars avars ctxmap spec.post.pure in

    (* only substitute if an existential element is wholly eliminated *)
    let eliminate_value v modvars =
      let vars = subst model v
        |> vars_of_sym_value
        |> vars_inter evars
      in
      (* after substitution, are there any existentials left here? *)
      (* if there are, then don't substitute into this value at all *)
      (* XXX if bind_pred fails, check here: might unbind an evar in pure *)
      if not (vars_is_empty vars) then
        vars_diff modvars (vars_of_sym_value v)
      else modvars
    in
    let eliminate_reg _ (v, _) modvars =
      eliminate_value v modvars
    in
    let eliminate_mem _ (_, _, region) modvars =
      BM.fold (fun _ -> eliminate_value) region modvars
    in
    let modvars =
      (model_vars model)
      |> SM.fold eliminate_reg spec.post.reg
      |> SM.fold eliminate_mem spec.post.mem
    in
    let model = model_project modvars model in

    if model_is_empty model then
      (* nothing more to unify: return *)
      Some spec
    else
      (* subst and unify again *)
      do_unify (subst_spec model spec)
  in
  do_unify spec

(* simplify specification by using pre-/post-conditions as context *)
let unify_spec (spec : sspec) : sspec =
  (* short-circuit if we're turned off *)
  if !settings.no_unify then
    spec
  else

  (* subst a model from pure precond *)
  let spec =
    match unify_pre spec with
    | Some spec -> spec
    | None ->
      failwith "unify_spec: detected inconsistent precondition"
  in

  (* subst a model from pure postcond *)
  let spec =
    match unify_post spec with
    | Some spec -> spec
    | None ->
      failwith "unify_spec: detected inconsistent postcondition"
  in

  spec
