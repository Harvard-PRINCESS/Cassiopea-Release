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

(* utilities for ITEs and choices *)

(* converting ITEs to choices *)
let rec dlist_of_ite :
  type a.
    a sym_value ->
    (bool sym_value * a sym_value) list * a sym_value =
  fun v ->
  match v.node with
  | SymIte (b, v1, v2) ->
    let (ls, tl) = dlist_of_ite v2 in
    ((b, v1) :: ls, tl)
  | _ -> ([], v)

(* converting choices to ITEs *)
let rec ite_of_dlist :
  type a.
    (bool sym_value * a sym_value) list * a sym_value ->
    a sym_value =
  fun (ls, tl) ->
  match ls with
  | [] -> tl
  | (b, v) :: ls' ->
    mk_ite b v (ite_of_dlist (ls', tl))

(* check whether a decision list is ordered per an ordering function *)
let dlist_ordered order (ls, tl) =
  let rec ordered =
    function
    | v1 :: v2 :: ls ->
      if order (snd v1) (snd v2) < 0 then
        ordered (v2 :: ls)
      else false
    | [(_, v)] -> order v tl < 0
    | [] -> true
  in
  ordered ls

(* merge two decision lists under a boolean condition *)
(* elements are maintained in sorted order per ordering function *)
(* items that compare identically are merged by merging function *)
let dlist_merge :
    ('a -> 'a -> int) -> (* ordering function *)
    (bool sym_value -> 'a -> 'a -> 'a) -> (* merging function *)
    bool sym_value ->
    (bool sym_value * 'a) list * 'a ->
    (bool sym_value * 'a) list * 'a ->
    (bool sym_value * 'a) list * 'a =
  fun cmp one b ls1 ls2 ->
  let rec merge (ls1, tl1) (ls2, tl2) =
    match (ls1, ls2) with
    | ([], []) ->
      let c = cmp tl1 tl2 in
      if c < 0 then
        ([(b, tl1)], tl2)
      else if c > 0 then
        ([(mk_unop LogNot b, tl2)], tl1)
      else
        ([], one b tl1 tl2)
    | ((b1, v1) :: ls1', []) ->
      let c = cmp v1 tl2 in
      if c < 0 then
        let (ls, tl) = merge (ls1', tl1) ([], tl2) in
        ((mk_binop LogAnd b b1, v1) :: ls, tl)
      else if c > 0 then
        ((mk_unop LogNot b, tl2) :: ls1, tl1)
      else
        ((mk_binop LogOr (mk_unop LogNot b) b1, one b v1 tl2) :: ls1', tl1)
    | ([], (b2, v2) :: ls2') ->
      let c = cmp v2 tl1 in
      if c < 0 then
        let (ls, tl) = merge ([], tl1) (ls2', tl2) in
        ((mk_binop LogAnd (mk_unop LogNot b) b2, v2) :: ls, tl)
      else if c > 0 then
        ((b, tl1) :: ls2, tl2)
      else
        ((mk_binop LogOr b b2, one b tl1 v2) :: ls2', tl2)
    | ((b1, v1) :: ls1', (b2, v2) :: ls2') ->
      let c = cmp v1 v2 in
      if c < 0 then
        let (ls, tl) = merge (ls1', tl1) (ls2, tl2) in
        ((mk_binop LogAnd b b1, v1) :: ls, tl)
      else if c > 0 then
        let (ls, tl) = merge (ls1, tl1) (ls2', tl2) in
        ((mk_binop LogAnd (mk_unop LogNot b) b2, v2) :: ls, tl)
      else
        let (ls, tl) = merge (ls1', tl1) (ls2', tl2) in
        ((mk_ite b b1 b2, one b v1 v2) :: ls, tl)
  in
  merge ls1 ls2

let order_ptr (i1, _) (i2, _) = compare i1 i2

let merge_ptr b (i1, o1) (i2, o2) =
  (* hoist identical constructors *)
  if i1 = i2 then
    (i1, mk_ite b o1 o2)
  else
    failwith "merge_ptr: got pointers to different regions"

(* canonicalizing words and pointers *)

(* canonicalized pointer is a SymChoose where
   1. each element is a single symbolic pointer
   2. each element points to a distinct memory region
   3. elements are ordered by memory region name *)
let is_canonicalized_ptr : (id * bits sym_value) sym_value -> bool =
  fun v ->
  match v.node with
  | SymVal (IsPtr _, _) -> true
  | SymChoose (ls, tl) ->
    let to_ptr (b, v) ls =
      match (v.node, ls) with
      | (SymVal (IsPtr _, v), Some ls) -> Some ((b, v) :: ls)
      | _ -> None
    in
    begin match tl.node with
    | SymVal (IsPtr _, tl) ->
      begin match List.fold_right to_ptr ls (Some []) with
      | Some ls -> dlist_ordered order_ptr (ls, tl)
      | None -> false
      end
    | _ -> false
    end
  | _ -> false

let canonicalize_ptr : int ->
    (id * bits sym_value) sym_value ->
    (id * bits sym_value) sym_value =
  fun l v ->
  let rec canonicalize' v =
    match v.node with
    | SymVal (IsPtr _, p) -> ([], p)
    | SymIte (b, v1, v2) ->
      let ls1 = canonicalize' v1 in
      let ls2 = canonicalize' v2 in
      dlist_merge order_ptr merge_ptr b ls1 ls2
    | SymChoose (ls, tl) ->
      let canonicalize_one (b, v) ls2 =
        let ls1 = canonicalize' v in
        dlist_merge order_ptr merge_ptr b ls1 ls2
      in
      List.fold_right canonicalize_one ls (canonicalize' tl)
    | _ -> failwith "canonicalize_ptr got impossible ptr value"
  in
  let (ls, tl) = canonicalize' v in
  let ls = List.map (fun (b, p) -> (b, mk_ptr p l)) ls in
  let tl = mk_ptr tl l in
  mk_choose ls tl

(* canonicalized word is an ITE where
   1. the left branch is all bitvecs
   2. the right branch is all pointers *)
let is_canonicalized_word : word_t sym_value -> bool =
  fun v ->
  match v.node with
  | SymVal (IsWord _, BitVec _) -> true
  | SymVal (IsWord _, BitPtr p) -> is_canonicalized_ptr p
  | SymIte (_, v1, v2) ->
    begin match (v1.node, v2.node) with
    | (SymVal (IsWord _, BitVec _), SymVal (IsWord _, BitPtr p)) ->
      is_canonicalized_ptr p
    | _ -> false
    end
  | _ -> false

let rec canonicalize_word : int -> word_t sym_value -> word_t sym_value =
  fun l v ->
  match v.node with
  | SymVal (IsWord _, BitVec _) -> v
  | SymVal (IsWord _, BitPtr v) ->
    mk_word (BitPtr (canonicalize_ptr l v)) l
  | SymIte (b, v1, v2) ->
    let v1 = canonicalize_word l v1 in
    let v2 = canonicalize_word l v2 in
    begin match (v1.node, v2.node) with
    (* hoist identical constructors *)
    | (SymVal (IsWord _, BitVec v1), SymVal (IsWord _, BitVec v2)) ->
      mk_word (BitVec (mk_ite b v1 v2)) l
    | (SymVal (IsWord _, BitPtr v1), SymVal (IsWord _, BitPtr v2)) ->
      mk_word (BitPtr (mk_ite b v1 v2)) l
    (* rotate misordered ITEs *)
    | (SymVal (IsWord _, BitPtr _), SymVal (IsWord _, BitVec _)) ->
      mk_ite (mk_unop LogNot b) v2 v1
    (* ITE canonicalization *)
    | (SymIte (b1, w1', w1''), SymIte (b2, w2', w2'')) ->
      let b' = mk_ite b b1 b2 in
      mk_ite b' (mk_ite b w1' w2') (mk_ite b w1'' w2'')
    | (SymVal (IsWord _, BitVec _), SymIte (b2, w2', w2'')) ->
      let b' = mk_binop LogOr b b2 in
      mk_ite b' (mk_ite b v1 w2') w2''
    | (SymIte (b1, w1', w1''), SymVal (IsWord _, BitVec _)) ->
      let b' = mk_binop LogOr (mk_unop LogNot b) b1 in
      mk_ite b' (mk_ite b w1' v2) w1''
    | (SymVal (IsWord _, BitPtr _), SymIte (b2', w2', w2'')) ->
      let b' = mk_binop LogAnd (mk_unop LogNot b) b2' in
      mk_ite b' w2' (mk_ite b v1 w2'')
    | (SymIte (b1', w1', w1''), SymVal (IsWord _, BitPtr _)) ->
      let b' = mk_binop LogAnd b b1' in
      mk_ite b' w1' (mk_ite b w1'' v2)
    (* nothing else of note *)
    | _ -> mk_ite b v1 v2
    end
  | SymChoose (ls, tl) ->
    canonicalize_word l (ite_of_dlist (ls, tl))
  | _ ->
    failwith "canonicalize_word: got invalid word value"
