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
open Hashcons

open Sym_ast
open Sym_cmp

(* hashconsing for symbolic values *)

(* hashing functions *)
let hc_hash_val : type a. a sym_ref_t -> a -> int =
  fun t v ->
  match t with
  | IsInt ->
    (BI.int_of_big_int (BI.mod_big_int v
      (BI.big_int_of_int 2147483647))) * 2 + 3
  | IsBool ->
    if v then 5 else 7
  | IsVec _ ->
    (BI.int_of_big_int
      (BI.mod_big_int
        (Bits.to_big_int v)
        (BI.big_int_of_int 2147483647))) * 11 + 13
  | IsPtr _ ->
    let (i, o) = v in (Hashtbl.hash i * 17 + o.hkey) * 19 + 23
  | IsLoc _ -> Hashtbl.hash v * 29 + 31
  | IsWord _ ->
    begin match v with
    | BitVec h -> h.hkey * 37 + 41
    | BitPtr p -> p.hkey * 43 + 47
    end

let hc_hash_unop : type a b. (a, b) sym_unop -> int =
  function
  | Neg -> 2
  | BNeg -> 31
  | LogNot -> 3
  | BitNot -> 5
  | BitIndex d -> 7 * d
  | BitSlice (d1, d2) -> 11 * d1 + 13 * d2 + 17 * d1 * d2
  | BitZeroExtend d -> 19 * d
  | BitToUInt -> 23
  | UIntToBit _ -> 29

let hc_hash_binop : type a b c. (a, b, c) sym_binop -> int =
  function
  | Add -> 2
  | Mul -> 5
  | Div -> 7
  | Pow -> 11
  | EqInt -> 13
  | EqVec -> 17
  | EqBool -> 19
  | Lt  -> 29
  | Gt  -> 31
  | BAdd -> 37
  | BMul -> 43
  | BLt -> 47
  | BGt -> 51
  | BSLt -> 53
  | BSGt -> 59
  | LShift -> 61
  | RShift -> 71
  | LRotate -> 73
  | RRotate -> 79
  | LogAnd -> 83
  | LogOr  -> 89
  | LogXor -> 97
  | BitAnd -> 101
  | BitOr  -> 103
  | BitXor -> 107

let hc_hash : type a. a sym_value' -> int =
  fun v ->
  match v with
  | SymVal (t, v) -> hc_hash_val t v
  | SymInt i -> i * 53 + 59
  | SymBool i -> i * 61 + 67
  | SymVec (i, _) -> i * 71 + 73
  | SymIte (b, v1, v2) ->
    ((b.hkey * 79 + v1.hkey) * 83 + v2.hkey) * 89 + 97
  | SymUnop (u, v) ->
    (v.hkey * 101 + hc_hash_unop u) * 103 + 107
  | SymBinop (b, v1, v2) ->
    ((v1.hkey * 109 + v2.hkey) * 113 + hc_hash_binop b) * 127 + 131
  | SymMultiop (b, ls, t, k) ->
    let hash_one z v =
      z * 137 + (v.hkey * 139 + hc_hash_binop b) * 149
    in
    List.fold_left hash_one (hc_hash_val t k) ls
  | SymChoose (ls, tl) ->
    let hash_one z (b, v) =
      z * 151 + (b.hkey * 157 + v.hkey) * 163
    in
    List.fold_left hash_one tl.hkey ls

(* hash table equality function *)
let hc_equal : type a. a sym_value' -> a sym_value' -> bool =
  fun v v' ->
  bool_of_cmp (cmp' v v')

(* maintain a separate table per type index *)
let tbl_int : bint sym_value' Hashcons.t = Hashcons.create 251
let tbl_bool : bool sym_value' Hashcons.t = Hashcons.create 251
let tbl_loc : id sym_value' Hashcons.t = Hashcons.create 251
let tbl_vec : bits sym_value' Hashcons.t = Hashcons.create 251
let tbl_ptr : (id * bits sym_value) sym_value' Hashcons.t = Hashcons.create 251
let tbl_word : word_t sym_value' Hashcons.t = Hashcons.create 251

let hashcons' : type a. a sym_ref_t -> a sym_value' -> a sym_value =
  fun t v ->
  let tbl : a sym_value' Hashcons.t =
    match t with
    | IsInt -> tbl_int
    | IsBool -> tbl_bool
    | IsLoc _ -> tbl_loc
    | IsVec _ -> tbl_vec
    | IsPtr _ -> tbl_ptr
    | IsWord _ -> tbl_word
  in
  Hashcons.hashcons hc_hash hc_equal tbl v

let hashcons : type a. a sym_value' -> a sym_value =
  fun v ->
  (* print table statistics *)
  (*let a,b,c,d,e,f = stats tbl_int in
  let _ = prerr_string ("int:" ^ (string_of_int c) ^ "\n") in
  let a,b,c,d,e,f = stats tbl_bit in
  let _ = prerr_string ("bit:" ^ (string_of_int c) ^ "\n") in
  let a,b,c,d,e,f = stats tbl_bool in
  let _ = prerr_string ("bool:" ^ (string_of_int c) ^ "\n") in
  let a,b,c,d,e,f = stats tbl_loc in
  let _ = prerr_string ("loc:" ^ (string_of_int c) ^ "\n") in*)
  hashcons' (typ_of_sym_value' v) v

let mk_int d = hashcons' IsInt (SymVal (IsInt, d))
let mk_bool b = hashcons' IsBool (SymVal (IsBool, b))
let mk_loc i l = hashcons' (IsLoc l) (SymVal (IsLoc l, i))
let mk_vec h = hashcons' (IsVec (Bits.width h)) (SymVal (IsVec (Bits.width h), h))
let mk_ptr p l = hashcons' (IsPtr l) (SymVal (IsPtr l, p))
let mk_word w l = hashcons' (IsWord l) (SymVal (IsWord l, w))

let mk_sym_int i = hashcons' IsInt (SymInt i)
let mk_sym_bool i = hashcons' IsBool (SymBool i)
let mk_sym_vec i l = hashcons' (IsVec l) (SymVec (i, l))

let mk_ite b v1 v2 = hashcons (SymIte (b, v1, v2))
let mk_unop u v = hashcons (SymUnop (u, v))
let mk_binop b v1 v2 = hashcons (SymBinop (b, v1, v2))

let mk_multiop b ls t v = hashcons (SymMultiop (b, ls, t, v))
let mk_choose ls tl = hashcons (SymChoose (ls, tl))

(* hashconsing for sym_ex_t *)

let hc_hash_ex (Ex (t, v)) =
  match t with
  | IsInt -> 2 * v.hkey
  | IsBool -> 3 * v.hkey
  | IsVec _ -> 5 * v.hkey
  | IsPtr _ -> 7 * v.hkey
  | IsLoc _ -> 11 * v.hkey
  | IsWord _ -> 13 * v.hkey

let hc_equal_ex ex1 ex2 = (cmp_ex' ex1 ex2) = 0

let tbl_ex : sym_ex_t' Hashcons.t = Hashcons.create 251

let hashcons_ex ex = Hashcons.hashcons hc_hash_ex hc_equal_ex tbl_ex ex

let ex_of_sym_value : type a. a sym_value -> sym_ex_t =
  fun v -> hashcons_ex (Ex (typ_of_sym_value v, v))
