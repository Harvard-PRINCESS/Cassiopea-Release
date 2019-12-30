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

(* manipulating sets of symbolic variables *)

(* CREATING SYMBOLIC VARIABLES *)
(* symbolic variable index counters *)
(* each symbolic variable gets a UID *)
let sym_ints = ref 0
let sym_bools = ref 0
let sym_vecs = ref 0

(* get the next symbolic variable *)
let next_sym_int () =
  let i = !sym_ints in
  sym_ints := i + 1;
  simpl (mk_sym_int i)

let next_sym_bool () =
  let i = !sym_bools in
  sym_bools := i + 1;
  simpl (mk_sym_bool i)

let next_sym_vec len =
  let i = !sym_vecs in
  sym_vecs := i + 1;
  simpl (mk_sym_vec i len)

(* get sets of symbolic variables involved in a symbolic expression *)
type vars = {
  int_set : IS.t;
  bool_set : IS.t;
  vec_set : int IM.t; (* mapping ID to length *)
}

let vars_empty = {
  int_set = IS.empty;
  bool_set = IS.empty;
  vec_set = IM.empty;
}

let hc_hash_vars sv = Hashtbl.hash sv

let hc_equal_vars sv1 sv2 =
  sv1.int_set = sv2.int_set &&
  sv1.bool_set = sv2.bool_set &&
  sv1.vec_set = sv2.vec_set

let tbl_vars : vars Hashcons.t = Hashcons.create 251

let hashcons_vars sv =
  (Hashcons.hashcons hc_hash_vars hc_equal_vars tbl_vars sv).node

let string_of_vars sv =
  let int_str =
    IS.elements sv.int_set
    |> List.map string_of_int
    |> String.concat " "
  in
  let bool_str =
    IS.elements sv.bool_set
    |> List.map string_of_int
    |> String.concat " "
  in
  let vec_str =
    IM.bindings sv.vec_set
    |> List.map (fun (i, l) -> (string_of_int i)^":"^(string_of_int l))
    |> String.concat " "
  in
  "INTS: "^int_str^"\n"^
  "BOOLS: "^bool_str^"\n"^
  "VECS: "^vec_str

let vars_is_empty sv =
  (IS.is_empty sv.int_set) &&
  (IS.is_empty sv.bool_set) &&
  (IM.is_empty sv.vec_set)

let vars_size sv =
  (IS.cardinal sv.int_set) +
  (IS.cardinal sv.bool_set) +
  (IM.cardinal sv.vec_set)

let vars_mem_int i sv = IS.mem i sv.int_set
let vars_mem_bool i sv = IS.mem i sv.bool_set
let vars_mem_vec i sv = IM.mem i sv.vec_set

(* union two sets of variables *)
let vars_union sv1 sv2 =
  let union_vecs i l1 l2 =
    if l1 <> l2 then
      failwith ("merging var sets: got two different lengths "^
                "for symbolic bitvector "^(string_of_int i)^
                ": "^(string_of_int l1)^" and "^(string_of_int l2))
    else
      Some l1
  in
  hashcons_vars
  { int_set = IS.union sv1.int_set sv2.int_set;
    bool_set = IS.union sv1.bool_set sv2.bool_set;
    vec_set = IM.union union_vecs sv1.vec_set sv2.vec_set; }

(* intersect two sets of variables *)
let vars_inter sv1 sv2 =
  let inter_vecs i l1 l2 =
    match (l1, l2) with
    | (Some l1, Some l2) ->
      if l1 <> l2 then
        failwith ("merging var sets: got two different lengths "^
                  "for symbolic bitvector "^(string_of_int i)^
                  ": "^(string_of_int l1)^" and "^(string_of_int l2))
      else
        Some l1
    | _ -> None
  in
  hashcons_vars
  { int_set = IS.inter sv1.int_set sv2.int_set;
    bool_set = IS.inter sv1.bool_set sv2.bool_set;
    vec_set = IM.merge inter_vecs sv1.vec_set sv2.vec_set; }

(* remove variables in sv2 from variables in sv1 *)
let vars_diff sv1 sv2 =
  hashcons_vars
  { int_set = IS.diff sv1.int_set sv2.int_set;
    bool_set = IS.diff sv1.bool_set sv2.bool_set;
    vec_set = IM.filter (fun k _ -> not (IM.mem k sv2.vec_set)) sv1.vec_set }

(* check if two sets of vars are disjoint *)
let vars_disjoint sv1 sv2 = vars_is_empty (vars_inter sv1 sv2)

(* get variables used in a symbolic value *)
let memo_vars = mk_memo_map ()
let rec vars_of_sym_value : type a. a sym_value -> vars =
  fun v ->
  match memo_map_mem memo_vars v with
  | Some v -> v
  | None ->
    memo_map_add memo_vars v (hashcons_vars
    begin match v.node with
    | SymVal (IsInt, _) -> vars_empty
    | SymVal (IsBool, _) -> vars_empty
    | SymVal (IsVec _, _) -> vars_empty
    | SymVal (IsPtr _, (_, v)) -> vars_of_sym_value v
    | SymVal (IsLoc _, _) -> vars_empty
    | SymVal (IsWord _, BitVec h) -> vars_of_sym_value h
    | SymVal (IsWord _, BitPtr p) -> vars_of_sym_value p
    | SymInt i -> { vars_empty with int_set = IS.singleton i }
    | SymBool i -> { vars_empty with bool_set = IS.singleton i }
    | SymVec (i, l) -> { vars_empty with vec_set = IM.singleton i l }
    | SymIte (b, v1, v2) ->
      let svb = vars_of_sym_value b in
      let sv1 = vars_of_sym_value v1 in
      let sv2 = vars_of_sym_value v2 in
      svb |> vars_union sv1 |> vars_union sv2
    | SymUnop (_, v) ->
      vars_of_sym_value v
    | SymBinop (_, v1, v2) ->
      let sv1 = vars_of_sym_value v1 in
      let sv2 = vars_of_sym_value v2 in
      vars_union sv1 sv2
    | SymMultiop (_, ls, _, _) ->
      let svls = List.map vars_of_sym_value ls in
      List.fold_left vars_union vars_empty svls
    | SymChoose (ls, tl) ->
      let pair (b, v) =
        vars_union (vars_of_sym_value b) (vars_of_sym_value v)
      in
      let svls = List.map pair ls in
      List.fold_left vars_union (vars_of_sym_value tl) svls
    end)
