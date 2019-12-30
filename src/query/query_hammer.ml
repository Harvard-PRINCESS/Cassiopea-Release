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

(* hammer simplifier *)

(* given an assumption over a set of universally quantified variables,
   go through a symbolic value and simplify any boolean that is
   always true or always false *)

let hammer_bool : bool sym_value -> bool sym_value -> bool sym_value =
  fun pred v ->
  match esolve (log_and pred v) with
  | None -> mk_bool false
  | Some _ ->
    match esolve (log_and pred (log_not v)) with
    | None -> mk_bool true
    | Some _ -> v

let hammer' :
  type a. memo_tmap ->
    vars -> bool sym_value ->
    a sym_value -> a sym_value =
  fun memo avars pred v ->
  let rec do_hammer : type a. a sym_value -> a sym_value =
    fun v ->
    match memo_tmap_mem memo v with
    | Some v -> v
    | None -> memo_tmap_add memo v
      begin let t = typ_of_sym_value v in
      let avars' = vars_diff (vars_of_sym_value v) avars in
      match t with
      (* if v contains only avars, then hammer it *)
      | IsBool when vars_is_empty avars' ->
        hammer_bool pred v
      | _ ->
        (* hammer subterms *)
        match v.node with
        | SymVal (IsPtr l, (i, o)) ->
          let o = do_hammer o in
          mk_ptr (i, o) l
        | SymVal (IsWord l, BitVec h) ->
          let h = do_hammer h in
          mk_word (BitVec h) l
        | SymVal (IsWord l, BitPtr p) ->
          let p = do_hammer p in
          mk_word (BitPtr p) l
        | SymIte (b, v1, v2) ->
          let b = do_hammer b in
          let v1 = do_hammer v1 in
          let v2 = do_hammer v2 in
          simpl' t (mk_ite b v1 v2)
        | SymUnop (u, v) ->
          let v = do_hammer v in
          simpl' t (mk_unop u v)
        | SymBinop (b, v1, v2) ->
          let v1 = do_hammer v1 in
          let v2 = do_hammer v2 in
          simpl' t (mk_binop b v1 v2)
        | SymMultiop (b, ls, _, k) ->
          let ls = List.map do_hammer ls in
          simpl' t (mk_multiop b ls t k)
        | SymChoose (ls, tl) ->
          let hammer_pair (b, v) = (do_hammer b, do_hammer v) in
          let ls = List.map hammer_pair ls in
          let tl = do_hammer tl in
          simpl' t (mk_choose ls tl)
        | _ -> v
      end
  in
  do_hammer v

let hammer :
  type a.
    vars -> bool sym_value ->
    a sym_value -> a sym_value =
  fun avars pred v ->
  let memo = mk_memo_tmap () in
  hammer' memo avars pred v
