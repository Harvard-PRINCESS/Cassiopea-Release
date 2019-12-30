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

let rec is_concrete : type a. a sym_value -> bool =
  fun v ->
  match v.node with
  | SymVal (IsInt, _) -> true
  | SymVal (IsBool, _) -> true
  | SymVal (IsVec _, _) -> true
  | SymVal (IsLoc _, _) -> true
  | SymVal (IsPtr _, (_, o)) -> is_concrete o
  | SymVal (IsWord _, BitVec h) -> is_concrete h
  | SymVal (IsWord _, BitPtr p) -> is_concrete p
  | _ -> false

(* concretization *)
let rec concretize : type a. a sym_value -> a option =
  fun v ->
  match v.node with
  | SymVal (IsInt, v) -> Some v
  | SymVal (IsBool, v) -> Some v
  | SymVal (IsVec _, v) -> Some v
  | SymVal (IsLoc _, v) -> Some v
  | SymVal (IsPtr _, (i, o)) ->
    begin match concretize o with
    | Some o -> Some (i, mk_vec o)
    | None -> None
    end
  | SymVal (IsWord _, BitVec h) ->
    begin match concretize h with
    | Some h -> Some (BitVec (mk_vec h))
    | None -> None
    end
  | SymVal (IsWord l, BitPtr p) ->
    begin match concretize p with
    | Some p -> Some (BitPtr (mk_ptr p l))
    | None -> None
    end
  | _ -> None

let symbolicize : type a. a sym_ref_t -> a -> a sym_value =
  fun t v ->
  match t with
  | IsInt -> mk_int v
  | IsBool -> mk_bool v
  | IsLoc l -> mk_loc v l
  | IsVec _ -> mk_vec v
  | IsPtr l -> mk_ptr v l
  | IsWord l -> mk_word v l

(* definitions of operators on concrete values *)

let concrete_unop : type a b. (a, b) sym_unop -> a -> b =
  fun u v ->
  let module CV = Concrete_value in
  match u with
  | Neg -> CV.neg v
  | BNeg ->
    let w = Bits.width v in
    Bits.sub (Bits.zero w) v
  | LogNot -> CV.log_not v
  | BitNot -> CV.bit_not v
  | BitIndex d -> Bits.get v (bint_of_int d)
  | BitSlice (d1, d2) -> CV.slice v d1 d2
  | BitZeroExtend d ->
    let w = Bits.width v + d in
    Bits.of_big_int w (Bits.to_big_int v)
  | BitToUInt -> Bits.to_big_int v
  | UIntToBit len -> Bits.of_big_int len v

let concrete_binop : type a b c. (a, b, c) sym_binop -> a -> b -> c =
  let module CV = Concrete_value in
  fun b v1 v2 ->
  match b with
  | Add -> CV.add v1 v2
  | Mul -> CV.mul v1 v2
  | Div -> CV.div v1 v2
  | Pow -> CV.pow v1 v2
  | EqInt -> CV.eq_int v1 v2
  | EqVec -> CV.eq_vec v1 v2
  | EqBool -> CV.eq_bool v1 v2
  | Lt -> CV.lt v1 v2
  | Gt -> CV.gt v1 v2
  | BAdd -> CV.badd_vec v1 v2
  | BMul -> CV.bmul v1 v2
  | BLt -> CV.blt v1 v2
  | BGt -> CV.bgt v1 v2
  | BSLt -> CV.bslt v1 v2
  | BSGt -> CV.bsgt v1 v2
  | LShift -> CV.lshift v1 v2
  | RShift -> CV.rshift v1 v2
  | LRotate -> Bits.rotl v1 (Bits.to_big_int v2)
  | RRotate -> Bits.rotr v1 (Bits.to_big_int v2)
  | LogAnd -> CV.log_and v1 v2
  | LogOr -> CV.log_or v1 v2
  | LogXor -> CV.log_xor v1 v2
  | BitAnd -> CV.bit_and v1 v2
  | BitOr -> CV.bit_or v1 v2
  | BitXor -> CV.bit_xor v1 v2
