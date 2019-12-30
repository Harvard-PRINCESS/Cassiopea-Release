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

(* comparison and type equality witnessing *)

(* this type allows equality to certify that the types are identical *)
type (_, _) cmp =
  | Same : ('a, 'a) cmp
  | Diff : ('a, 'b) cmp

let cmp_of_bool : bool -> ('a, 'b) cmp =
  fun v -> if v then Same else Diff

let bool_of_cmp : ('a, 'b) cmp -> bool =
  function
  | Same -> true
  | Diff -> false

let cmp_prim : 'a -> 'a -> ('b, 'c) cmp =
  fun v1 v2 ->
  let c = compare v1 v2 in
  cmp_of_bool (c = 0)

let cmp_typ : type a b. a sym_ref_t -> b sym_ref_t -> (a, b) cmp =
  fun t1 t2 ->
  match (t1, t2) with
  | (IsInt, IsInt) -> Same
  | (IsBool, IsBool) -> Same
  | (IsVec l1, IsVec l2) -> cmp_of_bool (l1 = l2)
  | (IsPtr l1, IsPtr l2) -> cmp_of_bool (l1 = l2)
  | (IsWord l1, IsWord l2) -> cmp_of_bool (l1 = l2)
  | (IsLoc l1, IsLoc l2) -> cmp_of_bool (l1 = l2)
  | _ -> Diff

let cmp_val :
  type a b.
    a sym_ref_t -> a ->
    b sym_ref_t -> b ->
    (a, b) cmp =
  fun t1 v1 t2 v2 ->
  match (t1, t2) with
  | (IsInt, IsInt) ->
    cmp_of_bool (BI.eq_big_int v1 v2)
  | (IsBool, IsBool) ->
    cmp_of_bool (v1 = v2)
  | (IsLoc _, IsLoc _) ->
    cmp_of_bool (v1 = v2)
  | (IsVec _, IsVec _) ->
    cmp_of_bool ((Bits.compare v1 v2) = 0)
  | (IsPtr _, IsPtr _) ->
    let (i1, o1) = v1 in
    let (i2, o2) = v2 in
    cmp_of_bool (i1 = i2 && o1.tag = o2.tag)
  | (IsWord _, IsWord _) ->
    begin match (v1, v2) with
    | (BitVec h1, BitVec h2) ->
      cmp_of_bool (h1.tag = h2.tag)
    | (BitPtr p1, BitPtr p2) ->
      cmp_of_bool (p1.tag = p2.tag)
    | _ -> Diff
    end
  | _ -> Diff

let cmp_unop :
  type a b c d.
    (a, b) sym_unop ->
    (c, d) sym_unop ->
    (a * b, c * d) cmp =
  fun u1 u2 ->
  match (u1, u2) with
  | (Neg, Neg) -> Same
  | (BNeg, BNeg) -> Same
  | (LogNot, LogNot) -> Same
  | (BitNot, BitNot) -> Same
  | (BitIndex i1, BitIndex i2) ->
    cmp_of_bool (i1 = i2)
  | (BitSlice (i1, i1'), BitSlice (i2, i2')) ->
    cmp_of_bool (i1 = i2 && i1' = i2')
  | (BitZeroExtend i, BitZeroExtend i') ->
    cmp_of_bool (i = i')
  | (BitToUInt, BitToUInt) -> Same
  | (UIntToBit i, UIntToBit i') ->
    cmp_of_bool (i = i')
  | _ -> Diff

let cmp_binop :
  type a b c d e f.
    (a, b, c) sym_binop ->
    (d, e, f) sym_binop ->
    (a * b * c, d * e * f) cmp =
  fun b1 b2 ->
  match (b1, b2) with
  | (Add, Add) -> Same
  | (Mul, Mul) -> Same
  | (Div, Div) -> Same
  | (Pow, Pow) -> Same
  | (EqInt, EqInt) -> Same
  | (EqVec, EqVec) -> Same
  | (EqBool, EqBool) -> Same
  | (Lt, Lt) -> Same
  | (Gt, Gt) -> Same
  | (BAdd, BAdd) -> Same
  | (BMul, BMul) -> Same
  | (BLt, BLt) -> Same
  | (BGt, BGt) -> Same
  | (BSLt, BSLt) -> Same
  | (BSGt, BSGt) -> Same
  | (LShift, LShift) -> Same
  | (RShift, RShift) -> Same
  | (LRotate, LRotate) -> Same
  | (RRotate, RRotate) -> Same
  | (LogAnd, LogAnd) -> Same
  | (LogOr, LogOr) -> Same
  | (LogXor, LogXor) -> Same
  | (BitAnd, BitAnd) -> Same
  | (BitOr, BitOr) -> Same
  | (BitXor, BitXor) -> Same
  | _ -> Diff

let cmp' : type a b. a sym_value' -> b sym_value' -> (a, b) cmp =
  fun v1 v2 ->
  match (v1, v2) with
  | (SymVal (t1, v1), SymVal (t2, v2)) -> cmp_val t1 v1 t2 v2
  | (SymInt i1, SymInt i2) -> cmp_of_bool (i1 = i2)
  | (SymVec (i1, _), SymVec (i2, _)) -> cmp_of_bool (i1 = i2)
  | (SymBool i1, SymBool i2) -> cmp_of_bool (i1 = i2)
  | (SymIte (b1, v1, v1'), SymIte (b2, v2, v2')) ->
    begin match cmp_typ (typ_of_sym_value v1) (typ_of_sym_value v2) with
    | Same -> cmp_of_bool (b1.tag = b2.tag && v1.tag = v2.tag && v1'.tag = v2'.tag)
    | Diff -> Diff
    end
  | (SymUnop (u1, v1), SymUnop (u2, v2)) ->
    begin match cmp_unop u1 u2 with
    | Same -> cmp_of_bool (v1.tag = v2.tag)
    | Diff -> Diff
    end
  | (SymBinop (b1, v1, v1'), SymBinop (b2, v2, v2')) ->
    begin match cmp_binop b1 b2 with
    | Same -> cmp_of_bool (v1.tag = v2.tag && v1'.tag = v2'.tag)
    | Diff -> Diff
    end
  | (SymMultiop (b1, ls1, t1, k1), SymMultiop (b2, ls2, t2, k2)) ->
    let rec cmp_ls =
      function
      | (v1 :: ls1', v2 :: ls2') ->
        if v1.tag = v2.tag then
          cmp_ls (ls1', ls2')
        else
          false
      | ([], []) -> true
      | _ -> false
    in
    begin match cmp_binop b1 b2 with
    | Same ->
      begin match cmp_val t1 k1 t2 k2 with
      | Same -> cmp_of_bool (cmp_ls (ls1, ls2))
      | Diff -> Diff
      end
    | Diff -> Diff
    end
  | (SymChoose (ls1, tl1), SymChoose (ls2, tl2)) ->
    let rec cmp_ls =
      function
      | ((b1, v1) :: ls1', (b2, v2) :: ls2') ->
        if b1.tag = b2.tag && v1.tag = v2.tag then
          cmp_ls (ls1', ls2')
        else
          false
      | ([], []) -> true
      | _ -> false
    in
    begin match cmp_typ (typ_of_sym_value tl1) (typ_of_sym_value tl2) with
    | Same -> cmp_of_bool (tl1.tag = tl2.tag && cmp_ls (ls1, ls2))
    | Diff -> Diff
    end
  | _ -> Diff

let cmp : type a b. a sym_value -> b sym_value -> (a, b) cmp =
  fun v v' -> cmp' v.node v'.node

let cmp_ex' v1 v2 =
  match (v1, v2) with
  | (Ex (IsInt, i1), Ex (IsInt, i2)) -> compare i1.tag i2.tag
  | (Ex (IsInt, _), _) -> -1 | (_, Ex (IsInt, _)) -> 1
  | (Ex (IsBool, i1), Ex (IsBool, i2)) -> compare i1.tag i2.tag
  | (Ex (IsBool, _), _) -> -1 | (_, Ex (IsBool, _)) -> 1
  | (Ex (IsLoc _, i1), Ex (IsLoc _, i2)) -> compare i1.tag i2.tag
  | (Ex (IsLoc _, _), _) -> -1 | (_, Ex (IsLoc _, _)) -> 1
  | (Ex (IsVec _, i1), Ex (IsVec _, i2)) -> compare i1.tag i2.tag
  | (Ex (IsVec _, _), _) -> -1 | (_, Ex (IsVec _, _)) -> 1
  | (Ex (IsPtr _, i1), Ex (IsPtr _, i2)) -> compare i1.tag i2.tag
  | (Ex (IsPtr _, _), _) -> -1 | (_, Ex (IsPtr _, _)) -> 1
  | (Ex (IsWord _, i1), Ex (IsWord _, i2)) -> compare i1.tag i2.tag

let cmp_ex v1 v2 = cmp_ex' v1.node v2.node
