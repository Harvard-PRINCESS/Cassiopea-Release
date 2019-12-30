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
open Symbase

open Sym_concrete
open Sym_multiop
open Sym_choose

(* simplifying symbolic expressions *)

(* memoizing simpl *)
let simpl_memo = mk_memo_tmap ()
let memo_simpl v v' =
  (* remember v -> v' and v' -> v' *)
  (* since rewriting should be idempotent *)
  memo_tmap_add simpl_memo v v'
  |> memo_tmap_add simpl_memo v'

(* simplify a symbolic value using algebraic rewrite rules *)
(* rewriting currently goes bottom-up: in some cases it might be
   more efficient to go top-down; to figure out later *)
let rec simpl : type a. a sym_value -> a sym_value =
  fun v -> simpl' (typ_of_sym_value v) v

and simpl' : type a. a sym_ref_t -> a sym_value -> a sym_value =
  fun t v ->
  match memo_tmap_mem' simpl_memo t v with
  | Some v -> v
  | None -> memo_simpl v
    begin match v.node with
    | SymVal (IsWord l, BitVec h) ->
      let h = simpl' (IsVec l) h in
      mk_word (BitVec h) l
    | SymVal (IsWord l, BitPtr p) ->
      let p = simpl' (IsPtr l) p in
      mk_word (BitPtr p) l
    | SymVal (IsPtr l, (i, o))->
      let o = simpl' (IsVec l) o in
      mk_ptr (i, o) l
    | SymVal (_, _) -> v
    | SymInt _ -> v
    | SymBool _ -> v
    | SymVec (_, _) -> v
    | SymUnop (u, v) -> simpl_unop t u v
    | SymBinop (b, v1, v2) -> simpl_binop t b v1 v2
    | SymIte (b, v1, v2) -> simpl_ite t b v1 v2
    | SymMultiop (b, ls, t, k) -> simpl_multiop t b ls k
    | SymChoose (ls, tl) -> simpl_choose t ls tl
    end

and simpl_unop :
  type a b. b sym_ref_t ->
    (a, b) sym_unop ->
    a sym_value ->
    b sym_value =
  fun t u v ->
  let v = simpl v in
  match concretize v with
  (* evaluate ops on concrete values *)
  | Some v -> symbolicize t (concrete_unop u v)
  (* simplify symbolic value *)
  | None ->
    (* map unop over multiop, construct another multiop from given binop,
       and recursively simplify *)
    let multi_app :
      type a.
        (a, b) sym_unop -> (b, b, b) sym_binop ->
        a sym_value list -> a ->
        b sym_value =
      fun u b ls k ->
      let ls = List.map (fun v -> simpl' t (mk_unop u v)) ls in
      let k = concrete_unop u k in
      simpl_multiop t b ls k
    in
    begin match (u, v.node) with
    (* collapse doubled negations *)
    | (Neg, SymUnop (Neg, v)) -> v
    | (BNeg, SymUnop (BNeg, v)) -> v
    | (LogNot, SymUnop (LogNot, v)) -> v
    | (BitNot, SymUnop (BitNot, v)) -> v
    (* commute negations inward *)
    | (Neg, SymMultiop (Add, ls, _, k)) -> multi_app Neg Add ls k
    | (BNeg, SymMultiop (BAdd, ls, _, k)) -> multi_app BNeg BAdd ls k
    | (LogNot, SymMultiop (LogAnd, ls, _, k)) -> multi_app LogNot LogOr ls k
    | (LogNot, SymMultiop (LogOr, ls, _, k)) -> multi_app LogNot LogAnd ls k
    | (LogNot, SymMultiop (LogXor, ls, _, k)) ->
      simpl_multiop t LogXor ls (concrete_unop LogNot k)
    | (BitNot, SymMultiop (BitAnd, ls, _, k)) -> multi_app BitNot BitOr ls k
    | (BitNot, SymMultiop (BitOr, ls, _, k)) -> multi_app BitNot BitAnd ls k
    | (BitNot, SymMultiop (BitXor, ls, _, k)) ->
      simpl_multiop t BitXor ls (concrete_unop BitNot k)
    (* commute bit-indexing inward *)
    | (BitIndex d, SymUnop (BitNot, v)) ->
      simpl_unop t LogNot (mk_unop (BitIndex d) v)
    | (BitIndex d, SymUnop (BitSlice (d1, _), v)) ->
      simpl_unop t (BitIndex (d + d1)) v
    | (BitIndex d, SymMultiop (BitAnd, ls, _, k)) ->
      multi_app (BitIndex d) LogAnd ls k
    | (BitIndex d, SymMultiop (BitOr, ls, _, k)) ->
      multi_app (BitIndex d) LogOr ls k
    | (BitIndex d, SymMultiop (BitXor, ls, _, k)) ->
      multi_app (BitIndex d) LogXor ls k
    (* TODO commute bit-slicing inward *)
    (* push operations into concrete ITEs *)
    | (_, SymIte (b, v1, v2)) ->
      begin match (concretize v1, concretize v2) with
      | (None, None) -> mk_unop u v
      | _ -> simpl_ite t b (mk_unop u v1) (mk_unop u v2)
      end
    (* no available rules *)
    | _ -> mk_unop u v
    end

and simpl_binop :
  type a b c. c sym_ref_t ->
    (a, b, c) sym_binop ->
    a sym_value ->
    b sym_value ->
    c sym_value =
  fun t b v1 v2 ->
  let v1 = simpl v1 in
  let v2 = simpl v2 in
  match (concretize v1, concretize v2) with
  (* evaluate ops on concrete values *)
  | (Some v1, Some v2) -> symbolicize t (concrete_binop b v1 v2)
  | _ ->
    begin match is_multiop b v1 v2 with
    | Some (b, v1, v2) ->
      (* multiop: convert and simplify *)
      let ls1 = list_of_binop b v1 in
      let ls2 = list_of_binop b v2 in
      let ls = List.merge multiop_order ls1 ls2 in
      simpl_multiop t b ls (id_of_multiop t b)
    | None ->
      (* simplify other symbolic value *)
      begin match (b, v1.node, v2.node) with
      (* short-circuit equalities *)
      | (EqInt, _, _) when v1.tag = v2.tag -> mk_bool true
      | (EqVec, _, _) when v1.tag = v2.tag -> mk_bool true
      | (EqBool, _, _) when v1.tag = v2.tag -> mk_bool true
      (* TODO Lt, Gt, BLt, BGt, BSLt, BSGt: remove elements appearing on both sides *)
      (* TODO EqInt, EqVec: remove elements appearing on both sides *)
      (* TODO LShift, RShift, LRotate, RRotate: merge constant shifts *)
      (* push operations into concrete ITEs *)
      | (_, _, SymIte (b', v1', v2')) ->
        begin match (concretize v1, concretize v1', concretize v2') with
        | (Some _, Some _, Some _) -> simpl_ite t b' (mk_binop b v1 v1') (mk_binop b v1 v2')
        | _ -> mk_binop b v1 v2
        end
      | (_, SymIte (b', v1', v2'), _) ->
        begin match (concretize v2, concretize v1', concretize v2') with
        | (Some _, Some _, Some _) -> simpl_ite t b' (mk_binop b v1' v2) (mk_binop b v2' v2)
        | _ -> mk_binop b v1 v2
        end
      (* no available rules *)
      | _ -> mk_binop b v1 v2
      end
    end

and simpl_ite :
  type a. a sym_ref_t ->
    bool sym_value ->
    a sym_value ->
    a sym_value ->
    a sym_value =
  fun t b v1 v2 ->
  (* simplify when branch condition is concrete true/false *)
  let b = simpl' IsBool b in
  match b.node with
  | SymVal (IsBool, true) -> simpl' t v1
  | SymVal (IsBool, false) -> simpl' t v2
  | _ ->
    let v1 = simpl' t v1 in
    let v2 = simpl' t v2 in
    (* identical branches *)
    if v1.tag = v2.tag then
      v1
    else
      begin match t with
      (* turn boolean ites into logical expressions *)
      | IsBool ->
        simpl' IsBool (mk_binop LogAnd
          (mk_binop LogOr (mk_unop LogNot b) v1)
          (mk_binop LogOr b v2))
      (* canonicalize pointer and word ITEs *)
      | IsPtr l ->
        let v = mk_ite b v1 v2 in
        if not (is_canonicalized_ptr v) then
          simpl' t (canonicalize_ptr l v)
        else v
      | IsWord l ->
        let v = mk_ite b v1 v2 in
        if not (is_canonicalized_word v) then
          simpl' t (canonicalize_word l v)
        else v
      | _ ->
        begin match (v1.node, v2.node) with
        (* hoist operations shared by both branches *)
        | (SymUnop (u1, v1'), SymUnop (u2, v2')) ->
          begin match cmp_unop u1 u2 with
          | Same ->
            simpl' t (mk_unop u1 (mk_ite b v1' v2'))
          | Diff ->
            mk_ite b v1 v2
          end
        | _ -> mk_ite b v1 v2
        end
      end

and simpl_multiop :
  type a. a sym_ref_t ->
    (a, a, a) sym_binop ->
    a sym_value list -> a ->
    a sym_value =
  fun t b ls k ->
  let ls = List.map (simpl' t) ls in
  multiop_rewrite b ls t k

and simpl_choose :
  type a. a sym_ref_t ->
    (bool sym_value * a sym_value) list ->
    a sym_value ->
    a sym_value =
  fun t ls tl ->
  (* short-circuit on true or false condition *)
  let simpl_pair (b, v) (ls, tl) =
    let b = simpl' IsBool b in
    let v = simpl' t v in
    match b.node with
    (* throw away remaining cases *)
    | SymVal (IsBool, true) -> ([], v)
    (* throw away this case *)
    | SymVal (IsBool, false) -> (ls, tl)
    (* attach simplified cond/value pair *)
    | _ -> ((b, v) :: ls, tl)
  in
  let (ls, tl) = List.fold_right simpl_pair ls ([], simpl' t tl) in
  match ls with
  (* if no choices are left, remove choose node *)
  | [] -> tl
  | _ ->
    begin match t with
    (* turn boolean chooses into logical expressions *)
    | IsBool -> simpl' IsBool (ite_of_dlist (ls, tl))
    (* canonicalize pointer and word chooses *)
    | IsPtr l ->
      let v = mk_choose ls tl in
      if not (is_canonicalized_ptr v) then
        simpl' t (canonicalize_ptr l v)
      else v
    | IsWord l ->
      let v = mk_choose ls tl in
      if not (is_canonicalized_word v) then
        simpl' t (canonicalize_word l v)
      else v
    | _ -> mk_choose ls tl
    end

(* TODO performance tracking *)
(* count how many nodes are eliminated *)
(* perhaps we can somehow count how many are eliminated per rule? *)
