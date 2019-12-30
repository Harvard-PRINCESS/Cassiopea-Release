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

(* symbolic values, symbolic expressions, and basic inspection utilities *)

type (_, _) sym_unop =
  | Neg : (bint, bint) sym_unop
  | BNeg : (bits, bits) sym_unop
  | LogNot : (bool, bool) sym_unop
  | BitNot : (bits, bits) sym_unop
  | BitIndex : int -> (bits, bool) sym_unop
  | BitSlice : (int * int) -> (bits, bits) sym_unop
  | BitZeroExtend : int -> (bits, bits) sym_unop
  | BitToUInt : (bits, bint) sym_unop
  | UIntToBit : int -> (bint, bits) sym_unop

type (_, _, _) sym_binop =
  | Add : (bint, bint, bint) sym_binop
  | Mul : (bint, bint, bint) sym_binop
  | Div : (bint, bint, bint) sym_binop
  | Pow : (bint, bint, bint) sym_binop
  | EqInt : (bint, bint, bool) sym_binop
  | EqVec : (bits, bits, bool) sym_binop
  | EqBool : (bool, bool, bool) sym_binop
  | Lt : (bint, bint, bool) sym_binop
  | Gt : (bint, bint, bool) sym_binop
  | BAdd : (bits, bits, bits) sym_binop
  | BMul : (bits, bits, bits) sym_binop
  | BLt : (bits, bits, bool) sym_binop
  | BGt : (bits, bits, bool) sym_binop
  | BSLt : (bits, bits, bool) sym_binop
  | BSGt : (bits, bits, bool) sym_binop
  | LShift : (bits, bits, bits) sym_binop
  | RShift : (bits, bits, bits) sym_binop
  | LRotate : (bits, bits, bits) sym_binop
  | RRotate : (bits, bits, bits) sym_binop
  | LogAnd : (bool, bool, bool) sym_binop
  | LogOr : (bool, bool, bool) sym_binop
  | LogXor : (bool, bool, bool) sym_binop
  | BitAnd : (bits, bits, bits) sym_binop
  | BitOr : (bits, bits, bits) sym_binop
  | BitXor : (bits, bits, bits) sym_binop

(* symbolic values *)
type _ sym_value' =
  (* symbolic value lift *)
  | SymVal : 'a sym_ref_t * 'a -> 'a sym_value'
  | SymInt : int -> bint sym_value'
  | SymBool : int -> bool sym_value'
  | SymVec : int(*id*) * int(*len*) -> bits sym_value'
  | SymUnop :
    ('a, 'b) sym_unop *
    'a sym_value ->
    'b sym_value'
  | SymBinop :
    ('a, 'b, 'c) sym_binop *
    'a sym_value *
    'b sym_value ->
    'c sym_value'
  | SymIte :
    bool sym_value *
    'a sym_value *
    'a sym_value ->
    'a sym_value'
  (* multiop: for commutative-associative operators *)
  (* SymMultiop (b, ls, t, k) represents:
     List.fold_left (fun rest v -> SymBinop (b, v, rest)) (SymVal (t, k)) (List.rev ls) *)
  | SymMultiop :
    ('a, 'a, 'a) sym_binop *
    'a sym_value list *
    'a sym_ref_t * 'a ->
    'a sym_value'
  (* choose: for ramified ITE trees *)
  (* SymChoose (ls, tl) represents:
     List.fold_left (fun rest (b, v) -> ite b v rest) tl (List.rev ls) *)
  | SymChoose :
    (bool sym_value * 'a sym_value) list *
    'a sym_value ->
    'a sym_value'

and 'a sym_value = 'a sym_value' hash_consed

(* type witness *)
(* "ref" is from "type reference" *)
and _ sym_ref_t =
  | IsInt : bint sym_ref_t
  | IsBool : bool sym_ref_t
  | IsLoc : int (*length*) -> id sym_ref_t
  | IsVec : int (*length*) -> bits sym_ref_t
  | IsPtr : int (*length*) -> (id * bits sym_value) sym_ref_t
  | IsWord : int (*length*) -> word_t sym_ref_t

and word_t =
  | BitVec of bits sym_value
  | BitPtr of (id * bits sym_value) sym_value

let rec string_of_sym_value : type a. a sym_value -> string =
  fun v -> string_of_sym_value' v.node

and string_of_sym_value' :
  type a.
    a sym_value' ->
    string =
  fun v ->
  match v with
  | SymVal (t, v) -> string_of_sym_val t v
  | SymInt i -> "int$"^(string_of_int i)
  | SymBool i -> "bool$"^(string_of_int i)
  | SymVec (i, l) -> "bv_"^(string_of_int l)^"$"^(string_of_int i)
  | SymIte (b, v1, v2) ->
    "(ite "^
      (string_of_sym_value b)^" "^
      (string_of_sym_value v1)^" "^
      (string_of_sym_value v2)^")"
  | SymUnop (u, v) ->
    "("^(string_of_sym_unop u)^" "^(string_of_sym_value v)^")"
  | SymBinop (b, v1, v2) ->
    "("^(string_of_sym_binop b)^" "^
      (string_of_sym_value v1)^" "^
      (string_of_sym_value v2)^")"
  | SymMultiop (b, ls, t, k) ->
    let ls' = ls
      |> List.map string_of_sym_value
      |> String.concat " "
    in
    "(multi "^(string_of_sym_binop b)^" { "^ls'^" "^
      (string_of_sym_val t k)^" })"
  | SymChoose (ls, tl) ->
    let string_of_pair (b, v) =
      (string_of_sym_value b)^" -> "^(string_of_sym_value v)
    in
    let ls' = ls
      |> List.map string_of_pair
      |> String.concat " | "
    in
    "(choose { "^ls'^" | _ -> "^(string_of_sym_value tl)^" })"

and string_of_sym_val :
  type a.
    a sym_ref_t -> a ->
    string =
  fun t v ->
  match t with
  | IsInt -> string_of_bint v
  | IsBool -> if v then "true" else "false"
  | IsLoc _ -> v
  | IsVec _ -> string_of_bits v
  | IsPtr _ -> let (i, o) = v in "["^i^":"^(string_of_sym_value o)^"]"
  | IsWord _ ->
    begin match v with
    | BitVec h -> "(bitvec "^(string_of_sym_value h)^")"
    | BitPtr p -> "(bitptr "^(string_of_sym_value p)^")"
    end

and string_of_sym_unop :
  type a b.
    (a, b) sym_unop ->
    string =
  function
  | Neg -> "-"
  | BNeg -> "b-"
  | LogNot -> "!"
  | BitNot -> "~"
  | BitIndex d -> "index["^(string_of_int d)^"]"
  | BitSlice (d1, d2) ->
    "slice["^
    (string_of_int d1)^":"^
    (string_of_int d2)^"]"
  | BitZeroExtend d ->
    "zero_extend "^(string_of_int d)
  | BitToUInt ->
    "bv2uint"
  | UIntToBit l ->
    "int2bv "^(string_of_int l)

and string_of_sym_binop :
  type a b c.
    (a, b, c) sym_binop ->
    string =
  function
  | Add -> "+"
  | Mul -> "*"
  | Div -> "/"
  | Pow -> "**"
  | EqInt -> "=="
  | EqVec -> "=="
  | EqBool -> "=="
  | Lt  -> "<"
  | Gt  -> ">"
  | BAdd -> "b+"
  | BMul -> "b*"
  | BLt -> "b<"
  | BGt -> "b>"
  | BSLt -> "bs<"
  | BSGt -> "bs>"
  | LShift -> "<<"
  | RShift -> ">>"
  | LRotate -> "rotl"
  | RRotate -> "rotr"
  | LogAnd -> "&&"
  | LogOr  -> "||"
  | LogXor -> "^^"
  | BitAnd -> "&"
  | BitOr  -> "|"
  | BitXor -> "^"

let rec width_of_vec : bits sym_value -> int =
  fun v -> width_of_vec' v.node

and width_of_vec' : bits sym_value' -> int =
  fun v ->
  match v with
  | SymVal (IsVec l, _) -> l
  | SymVec (_, l) -> l
  | SymIte (_, h, _) -> width_of_vec h
  | SymUnop (BNeg, v) -> width_of_vec v
  | SymUnop (BitNot, v) -> width_of_vec v
  | SymUnop (BitSlice (d1, d2), _) -> d2 - d1
  | SymUnop (BitZeroExtend d, v) -> d + width_of_vec v
  | SymUnop (UIntToBit l, _) -> l
  | SymBinop (BAdd, h, _) -> width_of_vec h
  | SymBinop (BMul, h, _) -> width_of_vec h
  | SymBinop (LShift, h, _) -> width_of_vec h
  | SymBinop (RShift, h, _) -> width_of_vec h
  | SymBinop (LRotate, h, _) -> width_of_vec h
  | SymBinop (RRotate, h, _) -> width_of_vec h
  | SymBinop (BitAnd, h, _) -> width_of_vec h
  | SymBinop (BitOr, h, _) -> width_of_vec h
  | SymBinop (BitXor, h, _) -> width_of_vec h
  | SymMultiop (_, _, IsVec l, _) -> l
  | SymChoose (_, tl) -> width_of_vec tl
  | _ -> failwith ("width_of_vec: impossible arg "^(string_of_sym_value' v))

let typ_of_sym_unop :
  type a b.
    (a, b) sym_unop ->
    a sym_value ->
    b sym_ref_t =
  fun u v ->
  match u with
  | Neg -> IsInt
  | BNeg -> IsVec (width_of_vec v)
  | LogNot -> IsBool
  | BitNot -> IsVec (width_of_vec v)
  | BitIndex _ -> IsBool
  | BitSlice _ -> IsVec (width_of_vec' (SymUnop (u, v)))
  | BitZeroExtend _ -> IsVec (width_of_vec' (SymUnop (u, v)))
  | BitToUInt -> IsInt
  | UIntToBit _ -> IsVec (width_of_vec' (SymUnop (u, v)))

let typ_of_sym_binop :
  type a b c.
    (a, b, c) sym_binop ->
    a sym_value ->
    b sym_value ->
    c sym_ref_t =
  fun b v _ ->
  match b with
  | Add -> IsInt
  | Mul -> IsInt
  | Div -> IsInt
  | Pow -> IsInt
  | EqInt -> IsBool
  | EqVec -> IsBool
  | EqBool -> IsBool
  | Lt -> IsBool
  | Gt -> IsBool
  | BAdd -> IsVec (width_of_vec v)
  | BMul -> IsVec (width_of_vec v)
  | BLt -> IsBool
  | BGt -> IsBool
  | BSLt -> IsBool
  | BSGt -> IsBool
  | LShift -> IsVec (width_of_vec v)
  | RShift -> IsVec (width_of_vec v)
  | LRotate -> IsVec (width_of_vec v)
  | RRotate -> IsVec (width_of_vec v)
  | LogAnd -> IsBool
  | LogOr -> IsBool
  | LogXor -> IsBool
  | BitAnd -> IsVec (width_of_vec v)
  | BitOr -> IsVec (width_of_vec v)
  | BitXor -> IsVec (width_of_vec v)

let rec typ_of_sym_value : type a. a sym_value -> a sym_ref_t =
  fun v -> typ_of_sym_value' v.node

and typ_of_sym_value' : type a. a sym_value' -> a sym_ref_t =
  fun v ->
  match v with
  | SymVal (t, _) -> t
  | SymInt _ -> IsInt
  | SymBool _ -> IsBool
  | SymVec (_, l) -> IsVec l
  | SymIte (_, v, _) -> typ_of_sym_value v
  | SymUnop (u, v) -> typ_of_sym_unop u v
  | SymBinop (b, v1, v2) -> typ_of_sym_binop b v1 v2
  | SymMultiop (_, _, t, _) -> t
  | SymChoose (_, tl) -> typ_of_sym_value tl

(* existential type *)
(* GADT existential whose contents have "some" type *)
type sym_ex_t' =
  | Ex : ('a sym_ref_t * 'a sym_value) -> sym_ex_t'
and sym_ex_t = sym_ex_t' hash_consed

let string_of_ex_t ex =
  match ex.node with
  | Ex (_, v) -> string_of_sym_value v
