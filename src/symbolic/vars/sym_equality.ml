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

(* extracting sets of equal values from predicates *)

type equality = {
  (* disjoint-set structure *)
  int_part : int IM.t ref;
  bool_part : int IM.t ref;
  vec_part : int IM.t ref;

  (* value reference *)
  int_vals : bint sym_value IM.t ref;
  bool_vals : bool sym_value IM.t ref;
  vec_vals : bits sym_value IM.t ref;
}

let equality_empty () =
  { int_part = ref IM.empty;
    bool_part = ref IM.empty;
    vec_part = ref IM.empty;

    int_vals = ref IM.empty;
    bool_vals = ref IM.empty;
    vec_vals = ref IM.empty; }

let equality_copy eq =
  { int_part = ref !(eq.int_part);
    bool_part = ref !(eq.bool_part);
    vec_part = ref !(eq.vec_part);

    int_vals = ref !(eq.int_vals);
    bool_vals = ref !(eq.bool_vals);
    vec_vals = ref !(eq.vec_vals); }

(* get appropriate partition for given type *)
let part_of_typ : type a. a sym_ref_t -> equality -> int IM.t ref =
  fun t eq ->
  match t with
  | IsInt -> eq.int_part
  | IsBool -> eq.bool_part
  | IsVec _ -> eq.vec_part
  | _ -> failwith "part_of_typ: got non-primitive type"

let vals_of_typ : type a. a sym_ref_t -> equality -> a sym_value IM.t ref =
  fun t eq ->
  match t with
  | IsInt -> eq.int_vals
  | IsBool -> eq.bool_vals
  | IsVec _ -> eq.vec_vals
  | _ -> failwith "vals_of_typ: got non-primitive type"

(* get representative for this value's partition *)
let rec equality_find' tag part =
  match IM.find_opt tag !part with
  | None ->
    part := IM.add tag tag !part; tag
  | Some tag' ->
    if tag = tag' then tag'
    else
      (* path compression *)
      let tag' = equality_find' tag' part in
      (part := IM.add tag tag' !part; tag')

let equality_find : type a. a sym_value -> equality -> int =
  fun v eq ->
  let t = typ_of_sym_value v in
  let part = part_of_typ t eq in
  let vals = vals_of_typ t eq in
  begin
  vals := IM.add v.tag v !vals;
  equality_find' v.tag part
  end

(* check if two values are known to be equal *)
(* (checks whether both values have same representative) *)
let equality_eq :
  type a.
    a sym_value ->
    a sym_value ->
    equality -> bool =
  fun v1 v2 eq ->
  let tag1 = equality_find v1 eq in
  let tag2 = equality_find v2 eq in
  tag1 = tag2

(* add equality between two values *)
let equality_equate' tag1 tag2 part =
  let tag1 = equality_find' tag1 part in
  let tag2 = equality_find' tag2 part in
  part := IM.add tag1 tag2 !part

let equality_equate :
  type a.
    a sym_value ->
    a sym_value ->
    equality -> equality =
  fun v1 v2 eq ->
  let eq = equality_copy eq in
  let t = typ_of_sym_value v1 in
  let part = part_of_typ t eq in
  let vals = vals_of_typ t eq in
  begin
  (* store values *)
  vals := IM.add v1.tag v1 !vals;
  vals := IM.add v2.tag v2 !vals;
  (* set tags equal *)
  equality_equate' v1.tag v2.tag part; eq
  end

(* produce equality set representing union & congruence closure *)
let equality_union' part1 part2 =
  (* add equalities in part2 to part1 *)
  let part = ref !part1 in
  let equate_one tag _ =
    let tag1 = equality_find' tag part1 in
    let tag2 = equality_find' tag part2 in
    equality_equate' tag1 tag2 part
  in
  IM.iter equate_one !part2;
  part

let equality_union eq1 eq2 =
  let union tag v1 v2 =
    (* all these values should be equal *)
    if tag <> v1.tag || v1.tag <> v2.tag then
      failwith "equality_union: bad tags in equality vals"
    else
      Some v1
  in
  { int_part = equality_union' eq1.int_part eq2.int_part;
    bool_part = equality_union' eq1.bool_part eq2.bool_part;
    vec_part = equality_union' eq1.vec_part eq2.vec_part;

    int_vals = ref (IM.union union !(eq1.int_vals) !(eq2.int_vals));
    bool_vals = ref (IM.union union !(eq1.bool_vals) !(eq2.bool_vals));
    vec_vals = ref (IM.union union !(eq1.vec_vals) !(eq2.vec_vals)); }

(* produce equality set representing intersection *)
let equality_inter' part1 part2 =
  (* mark each value in part1, part2 with its representative *)
  (* if coincidences found, add equality *)
  let part = ref IM.empty in
  let equate_one tag _ sets =
    let tag1 = equality_find' tag part1 in
    let tag2 = equality_find' tag part2 in
    match IM.find_opt tag1 sets with
    | None -> IM.add tag1 (IM.singleton tag2 tag) sets
    | Some set ->
      begin match IM.find_opt tag2 set with
      | None -> IM.add tag1 (IM.add tag2 tag set) sets
      | Some tag' -> equality_equate' tag tag' part; sets
      end
  in
  let sets = IM.empty in
  let sets = IM.fold equate_one !part1 sets in
  let _ = IM.fold equate_one !part2 sets in
  part

let equality_inter eq1 eq2 =
  let union tag v1 v2 =
    (* all these values should be equal *)
    if tag <> v1.tag || v1.tag <> v2.tag then
      failwith "equality_inter: bad tags in equality vals"
    else
      Some v1
  in
  { int_part = equality_inter' eq1.int_part eq2.int_part;
    bool_part = equality_inter' eq1.bool_part eq2.bool_part;
    vec_part = equality_inter' eq1.vec_part eq2.vec_part;

    int_vals = ref (IM.union union !(eq1.int_vals) !(eq2.int_vals));
    bool_vals = ref (IM.union union !(eq1.bool_vals) !(eq2.bool_vals));
    vec_vals = ref (IM.union union !(eq1.vec_vals) !(eq2.vec_vals)); }

(* TODO interpolation for boolean equalities *)

(* extract equality sets from a predicate *)
(* None indicates an unsatisfiable predicate *)
let eq_memo = mk_memo_map ()
let rec equality_of_pred (p : bool sym_value) : equality =
  match memo_map_mem eq_memo p with
  | Some model -> model
  | None ->
    memo_map_add eq_memo p
    begin
    let eq = equality_equate p (mk_bool true) (equality_empty ()) in
    match p.node with
    | SymUnop (LogNot, v) ->
      equality_equate v (mk_bool false) eq
    | SymBinop (EqInt, v1, v2) ->
      equality_equate v1 v2 eq
    | SymBinop (EqBool, v1, v2) ->
      equality_equate v1 v2 eq
    | SymBinop (EqVec, v1, v2) ->
      equality_equate v1 v2 eq
    | SymMultiop (LogAnd, ls, _, _) ->
      List.map equality_of_pred ls
      |> List.fold_left equality_union eq
    | SymMultiop (LogOr, ls, _, _) ->
      List.map equality_of_pred ls
      |> List.fold_left equality_inter eq
    | _ -> eq
    end

(* obtain set of values equal to given value *)
let eqset_of_value' tag part vals =
  let add_one tag' _ set =
    if tag = equality_find' tag' part then
      IS.add tag' set
    else set
  in
  IM.fold add_one !vals IS.empty

let eqset_of_value : type a. a sym_value -> equality -> a sym_value list =
  fun v eq ->
  let tag = equality_find v eq in
  let part = part_of_typ (typ_of_sym_value v) eq in
  let vals = vals_of_typ (typ_of_sym_value v) eq in
  eqset_of_value' tag part vals
  |> IS.remove v.tag (* don't return same value in eqset TODO janky *)
  |> IS.elements
  |> List.map
    (fun tag ->
      match IM.find_opt tag !vals with
      | Some v -> v
      | None -> failwith "eqset_of_value: tag missing from vars")
