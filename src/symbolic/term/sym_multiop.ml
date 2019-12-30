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

(* utilities for SymMultiop *)
(* converting binops to multiops; algebraic information *)

(* is this a multiop? commutative/associative binops *)
(* returns inputs but proves that they are of same type *)
let is_multiop : type a b c.
    (a, b, c) sym_binop -> a sym_value -> b sym_value ->
    ((c, c, c) sym_binop * c sym_value * c sym_value) option =
  fun b v1 v2 ->
  match b with
  | Add -> Some (Add, v1, v2)
  | Mul -> Some (Mul, v1, v2)
  | BAdd -> Some (BAdd, v1, v2)
  | BMul -> Some (BMul, v1, v2)
  | LogAnd -> Some (LogAnd, v1, v2)
  | LogOr -> Some (LogOr, v1, v2)
  | LogXor -> Some (LogXor, v1, v2)
  | BitAnd -> Some (BitAnd, v1, v2)
  | BitOr -> Some (BitOr, v1, v2)
  | BitXor -> Some (BitXor, v1, v2)
  | _ -> None

let multiop_is_idempotent : type a. (a, a, a) sym_binop -> bool =
  function
  | LogAnd -> true
  | LogOr -> true
  | BitAnd -> true
  | BitOr -> true
  | _ -> false

let multiop_is_involutive : type a. (a, a, a) sym_binop -> bool =
  function
  | LogXor -> true
  | BitXor -> true
  | _ -> false

(* identity elements for multiops *)
let id_of_multiop : type a. a sym_ref_t -> (a, a, a) sym_binop -> a =
  fun t ->
  let fail s =
    failwith ("id_of_multiop: type of "^s^" should be an IsVec")
  in
  function
  | Add -> BI.zero_big_int
  | Mul -> BI.unit_big_int
  | BAdd ->
    begin match t with
    | IsVec l -> Bits.zero l
    | _ -> fail "BAdd"
    end
  | BMul ->
    begin match t with
    | IsVec l -> Bits.of_big_int l BI.unit_big_int
    | _ -> fail "BMul"
    end
  | LogAnd -> true
  | LogOr -> false
  | LogXor -> false
  | BitAnd ->
    begin match t with
    | IsVec l -> Bits.not (Bits.zero l)
    | _ -> fail "BitAnd"
    end
  | BitOr ->
    begin match t with
    | IsVec l -> Bits.zero l
    | _ -> fail "BitOr"
    end
  | BitXor ->
    begin match t with
    | IsVec l -> Bits.zero l
    | _ -> fail "BitXor"
    end
  | _ -> failwith "id_of_multiop: got a non-multiop"

(* absorbing elements for multiops *)
let zero_of_multiop : type a. a sym_ref_t -> (a, a, a) sym_binop -> a option =
  let fail s =
    failwith ("zero_of_multiop: type of "^s^" should be an IsVec")
  in
  fun t ->
  function
  | Mul -> Some BI.zero_big_int
  | BMul ->
    begin match t with
    | IsVec l -> Some (Bits.zero l)
    | _ -> fail "BMul"
    end
  | LogAnd -> Some false
  | LogOr -> Some true
  | BitAnd ->
    begin match t with
    | IsVec l -> Some (Bits.zero l)
    | _ -> fail "BitAnd"
    end
  | BitOr ->
    begin match t with
    | IsVec l -> Some (Bits.not (Bits.zero l))
    | _ -> fail "BitOr"
    end
  | _ -> None

(* canonical ordering for elements in a multiop *)
(* sort by size smallest to largest, then by tag value *)
let multiop_order v1 v2 =
  let sz1 = depth_of_sym_value v1 in
  let sz2 = depth_of_sym_value v2 in
  if sz1 < sz2 then
    -1
  else if sz1 > sz2 then
    1
  else
    compare v1.tag v2.tag

(* check if a list contains a given symbolic value *)
let multils_contains : type a. a sym_value -> a sym_value list -> bool =
  fun v ls -> List.exists (fun v' -> v.tag = v'.tag) ls

(* sort list by canonical ordering *)
let multils_sort : type a. a sym_value list -> a sym_value list =
  fun ls -> List.sort multiop_order ls

(* deduplicate list by tag *)
let rec multils_uniq : type a. a sym_value list -> a sym_value list =
  function
  | v1 :: v2 :: ls' when v1.tag = v2.tag -> multils_uniq (v1 :: ls')
  | v :: ls' -> v :: multils_uniq ls'
  | [] -> []

(* remove pairs of occurrences by tag *)
let rec multils_involute : type a. a sym_value list -> a sym_value list =
  function
  | v1 :: v2 :: ls' when v1.tag = v2.tag -> multils_involute ls'
  | v :: ls' -> v :: multils_uniq ls'
  | [] -> []

(* convert binop to multiop list *)
(* list comes back sorted *)
let rec list_of_binop :
  type a.
    (a, a, a) sym_binop ->
    a sym_value ->
    a sym_value list =
  fun b v ->
  match v.node with
  | SymBinop (b', v1, v2) ->
    begin match cmp_binop b b' with
    | Same -> List.merge multiop_order (list_of_binop b v1) (list_of_binop b v2)
    | Diff -> [v]
    end
  | SymMultiop (b', ls, t, k) ->
    begin match cmp_binop b b' with
    | Same -> List.merge multiop_order ls [symbolicize t k]
    | Diff -> [v]
    end
  | _ -> [v]

(* multiop simplification subroutine *)
let multiop_rewrite :
  type a. (a, a, a) sym_binop ->
    a sym_value list ->
    a sym_ref_t -> a ->
    a sym_value =
  fun b ls t k ->
  (* gather constants into tail value *)
  let simpl_concrete v (ls, k) =
    match concretize v with
    | Some v ->
      (ls, concrete_binop b v k)
    | None ->
      (v :: ls, k)
  in
  let (ls, k) = List.fold_right simpl_concrete ls ([], k) in
  (* if we gathered a zero, return zero *)
  let is_zero =
    match zero_of_multiop t b with
    | Some zero ->
      begin match cmp_val t k t zero with
      | Same -> true
      | Diff -> false
      end
    | _ -> false
  in
  if is_zero then
    symbolicize t k
  else
    (* sort the list *)
    let ls = multils_sort ls in
    (* if op is idempotent, remove duplicates *)
    let ls =
      if multiop_is_idempotent b then
        multils_uniq ls
      else ls
    in
    (* if op is involutive, remove even numbers of identical elements *)
    let ls =
      if multiop_is_involutive b then
        multils_involute ls
      else ls
    in
    match ls with
    (* if there's nothing left, remove multiop node *)
    | [] -> symbolicize t k
    (* if there's just one thing op'd with identity, remove multiop node *)
    | [v] ->
      begin match cmp_val t k t (id_of_multiop t b) with
      | Same -> v
      | Diff -> mk_multiop b ls t k
      end
    | _ -> mk_multiop b ls t k
