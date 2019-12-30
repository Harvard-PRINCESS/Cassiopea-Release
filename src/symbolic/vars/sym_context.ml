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
open Symbolic

open Sym_vars
open Sym_model

(* contexts and extracting information from contexts *)

(* use a context to maximally simplify an expression *)
(* TODO extend to non-boolean expressions using extracted equalities *)
let ctx_subst_memo = mk_memo_map ()
let rec context_subst (ctx : bool sym_value) (p : bool sym_value) =
  (* get memoization table associated with this context *)
  let memo =
    match memo_map_mem ctx_subst_memo ctx with
    | Some memo -> memo
    | None -> memo_map_add ctx_subst_memo ctx (mk_memo_map ())
  in
  (* recursive simplification *)
  let rec do_subst (p : bool sym_value) =
    match memo_map_mem memo p with
    | Some p -> p
    | None ->
      memo_map_add memo p
      begin match ctx.node with
      (* assuming an AND *)
      | SymMultiop (LogAnd, ls, _, _) ->
        (* simplify successively assuming each subterm *)
        List.fold_left (fun p' ctx' -> context_subst ctx' p') p ls

      (* assuming an OR *)
      | SymMultiop (LogOr, _, _, _) ->
        begin match p.node with
        | SymMultiop (LogAnd, ls', t', k') ->
          let ls' = List.map do_subst ls' in
          let p = simpl (mk_multiop LogAnd ls' t' k') in
          (* check ctx => ~p by p => ~ctx *)
          if (context_subst p ctx).tag = (mk_bool false).tag then
            mk_bool false
          else p
        | SymMultiop (LogOr, ls', t', k') ->
          let ls' = List.map do_subst ls' in
          let p = simpl (mk_multiop LogOr ls' t' k') in
          let p' = simpl (mk_unop LogNot p) in
          (* check ctx => p by ~p => ~ctx *)
          if (context_subst p' ctx).tag = (mk_bool false).tag then
            mk_bool true
          else p
        | _ ->
          let p' = simpl (mk_unop LogNot p) in
          if (context_subst p' ctx).tag = (mk_bool false).tag then
            mk_bool true
          else if (context_subst p ctx).tag = (mk_bool false).tag then
            mk_bool false
          else p
        end

      (* assumption is a LITERAL *)
      | _ ->
        begin match p.node with
        | SymMultiop (LogAnd, ls, t, k) ->
          let ls = List.map do_subst ls in
          simpl (mk_multiop LogAnd ls t k)
        | SymMultiop (LogOr, ls, t, k) ->
          let ls = List.map do_subst ls in
          simpl (mk_multiop LogOr ls t k)
        | _ ->
          (* check if ctx term is identical or complement *)
          if ctx.tag = p.tag then
            mk_bool true
          else if ctx.tag = (simpl (mk_unop LogNot p)).tag then
            mk_bool false
          else p
        end
      end
  in
  do_subst p

(* simplify a boolean expression *)
(* use each element to reduce each other element *)
(* TODO extend to non-boolean expressions using extracted equalities *)
let ctx_reduce_memo = mk_memo_map ()
let rec context_reduce (p : bool sym_value) =
  match memo_map_mem ctx_reduce_memo p with
  | Some p -> p
  | None ->
    memo_map_add ctx_reduce_memo p
    begin match p.node with
    | SymMultiop (LogAnd, ls, t, k) ->
      let ls = List.map context_reduce ls in
      (* assume each element and use to simplify all others *)
      let rec reduce_one hd tl =
        match tl with
        | h :: tl ->
          let hd = h :: (List.map (context_subst h) hd) in
          let tl = List.map (context_subst h) tl in
          reduce_one hd tl
        | [] -> hd
      in
      let p' = simpl (mk_multiop LogAnd (reduce_one [] ls) t k) in
      (* TODO yank out common elements of sub-disjunctions *)
      (* if anything simplified successfully, repeat *)
      if p.tag <> p'.tag then
        context_reduce p'
      else p'
    | SymMultiop (LogOr, ls, t, k) ->
      let ls = List.map context_reduce ls in
      (* assume NOT each element and use to simplify all others *)
      let rec reduce_one hd tl =
        match tl with
        | h :: tl ->
          let h' = simpl (mk_unop LogNot h) in
          let hd = h :: (List.map (context_subst h') hd) in
          let tl = List.map (context_subst h') tl in
          reduce_one hd tl
        | [] -> hd
      in
      let p' = simpl (mk_multiop LogOr (reduce_one [] ls) t k) in
      (* TODO yank out common elements of sub-conjunctions *)
      (* if anything simplified successfully, repeat *)
      if p.tag <> p'.tag then
        context_reduce p'
      else p'
    | _ -> p
    end

let context_and ctx1 ctx2 =
  mk_binop LogAnd ctx1 ctx2
  |> simpl |> context_reduce

let context_or ctx1 ctx2 =
  mk_binop LogOr ctx1 ctx2
  |> simpl |> context_reduce

(* given a context and a node, obtain contexts for node children *)
let context_propagate :
  type a. a sym_value ->
    bool sym_value ->
    bool sym_value SVM.t =
  fun v ctx ->
  match v.node with
  | SymVal (IsInt, _) -> SVM.empty
  | SymVal (IsBool, _) -> SVM.empty
  | SymVal (IsLoc _, _) -> SVM.empty
  | SymVal (IsVec _, _) -> SVM.empty
  | SymVal (IsPtr _, (_, o)) ->
    SVM.singleton (ex_of_sym_value o) ctx
  | SymVal (IsWord _, BitVec w) ->
    SVM.singleton (ex_of_sym_value w) ctx
  | SymVal (IsWord _, BitPtr w) ->
    SVM.singleton (ex_of_sym_value w) ctx
  | SymInt _ -> SVM.empty
  | SymBool _ -> SVM.empty
  | SymVec (_, _) -> SVM.empty
  | SymUnop (_, v') -> SVM.singleton (ex_of_sym_value v') ctx
  | SymBinop (LogAnd, v1, v2) ->
    let ctx' = context_and v1 ctx in
    SVM.empty
    |> SVM.add (ex_of_sym_value v1) ctx
    |> SVM.add (ex_of_sym_value v2) ctx'
  | SymBinop (LogOr, v1, v2) ->
    let ctx' = context_and (simpl (mk_unop LogNot v1)) ctx in
    SVM.empty
    |> SVM.add (ex_of_sym_value v1) ctx
    |> SVM.add (ex_of_sym_value v2) ctx'
  | SymBinop (_, v1, v2) ->
    SVM.empty
    |> SVM.add (ex_of_sym_value v1) ctx
    |> SVM.add (ex_of_sym_value v2) ctx
  | SymIte (b, v1, v2) ->
    let ctx' = context_and b ctx in
    let ctx'' = context_and b ctx' in
    SVM.empty
    |> SVM.add (ex_of_sym_value b) ctx
    |> SVM.add (ex_of_sym_value v1) ctx'
    |> SVM.add (ex_of_sym_value v2) ctx''
  | SymMultiop (LogAnd, ls, _, _) ->
    let propagate_one (ctx, ctxmap) v =
      let ctx' = context_and v ctx in
      let ctxmap' = SVM.add (ex_of_sym_value v) ctx ctxmap in
      (ctx', ctxmap')
    in
    let (_, ctxmap) = List.fold_left propagate_one (ctx, SVM.empty) ls in
    ctxmap
  | SymMultiop (LogOr, ls, _, _) ->
    let propagate_one (ctx, ctxmap) v =
      let ctx' = context_and (simpl (mk_unop LogNot v)) ctx in
      let ctxmap' = SVM.add (ex_of_sym_value v) ctx ctxmap in
      (ctx', ctxmap')
    in
    let (_, ctxmap) = List.fold_left propagate_one (ctx, SVM.empty) ls in
    ctxmap
  | SymMultiop (_, ls, _, _) ->
    let propagate_one ctxmap v =
      SVM.add (ex_of_sym_value v) ctx ctxmap
    in
    List.fold_left propagate_one SVM.empty ls
  | SymChoose (ls, tl) ->
    let propagate_pair (ctx, ctxmap) (b, v) =
      let ctx' = context_and b ctx in
      let ctx'' = context_and (simpl (mk_unop LogNot b)) ctx in
      let ctxmap' = ctxmap
        |> SVM.add (ex_of_sym_value b) ctx
        |> SVM.add (ex_of_sym_value v) ctx'
      in
      (ctx'', ctxmap')
    in
    let (ctx, ctxmap) = List.fold_left propagate_pair (ctx, SVM.empty) ls in
    SVM.add (ex_of_sym_value tl) ctx ctxmap

(* produce a map associating values with their contexts *)
(* TODO weak and strong versions *)
let context_of_dag (dag : dag) =
  (* initialize roots with empty contexts *)
  let add_root root ctxmap =
    SVM.add root (mk_bool true) ctxmap
  in
  let ctxmap = SVS.fold add_root dag.roots SVM.empty in

  (* add contexts *)
  let add_context node _ ctxmap =
    let ctx =
      match SVM.find_opt node ctxmap with
      | Some ctx -> ctx
      | None -> failwith "context_of_dag: missing node context"
    in
    match node.node with
    | Ex (_, v) ->
      (* propagate contexts to children *)
      context_propagate v ctx
      (* add these contexts to children *)
      |> SVM.union (fun _ ctx1 ctx2 -> Some (context_or ctx1 ctx2)) ctxmap
  in
  dag_fold_left add_context ctxmap dag

(* context-aware simplification *)
let contextual : type a. a sym_value -> a sym_value =
  fun v -> simpl v (* TODO *)
