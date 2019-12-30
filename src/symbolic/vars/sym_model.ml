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

(* mappings for substituting symbolic variables *)

type model = {
  int_model : bint sym_value IM.t;
  bool_model : bool sym_value IM.t;
  vec_model : bits sym_value IM.t;
}

let model_empty = {
  int_model = IM.empty;
  bool_model = IM.empty;
  vec_model = IM.empty;
}

let string_of_model model =
  let pair_to_string (k, v) =
    (string_of_int k)^" : "^(string_of_sym_value v)
  in
  "SYMBOLIC INTS:\n"^
  (model.int_model
    |> IM.bindings
    |> List.map pair_to_string
    |> String.concat "\n")^"\n\n"^
  "SYMBOLIC BOOLS:\n"^
  (model.bool_model
    |> IM.bindings
    |> List.map pair_to_string
    |> String.concat "\n")^"\n\n"^
  "SYMBOLIC VECS:\n"^
  (model.vec_model
    |> IM.bindings
    |> List.map pair_to_string
    |> String.concat "\n")

let model_is_empty m =
  (IM.is_empty m.int_model) &&
  (IM.is_empty m.bool_model) &&
  (IM.is_empty m.vec_model)

(* get variables substituted by model *)
let model_vars m =
  { int_set = IM.bindings m.int_model |> List.rev_map fst |> IS.of_list;
    bool_set = IM.bindings m.bool_model |> List.rev_map fst |> IS.of_list;
    vec_set = IM.map (fun v -> width_of_vec v) m.vec_model; }

(* get variables AFTER substituting by model *)
let model_vars' m =
  let get_vars m =
    IM.bindings m |>
    List.rev_map snd |>
    List.rev_map vars_of_sym_value |>
    List.fold_left vars_union vars_empty
  in
  (get_vars m.int_model) |> vars_union
  (get_vars m.bool_model) |> vars_union
  (get_vars m.vec_model)

let model_get_int i m = IM.find_opt i m.int_model
let model_get_bool i m = IM.find_opt i m.bool_model
let model_get_vec i m = IM.find_opt i m.vec_model

let model_add_int i v m = { m with int_model = IM.add i v m.int_model }
let model_add_bool i v m = { m with bool_model = IM.add i v m.bool_model }
let model_add_vec i v m = { m with vec_model = IM.add i v m.vec_model }

(* return a model containing every mapping in both models *)
(* None indicates that inconsistent mappings were found *)
let model_union m1 m2 =
  (* check map consistency *)
  let check map i v =
    match IM.find_opt i map with
    | Some v' -> v.tag <> v'.tag
    | None -> false
  in
  if (IM.exists (check m2.int_model) m1.int_model) ||
     (IM.exists (check m2.bool_model) m1.bool_model) ||
     (IM.exists (check m2.vec_model) m1.vec_model) then
    (print_string ("INCONSISTENCY:\n"^(string_of_model m1)^"\n"^(string_of_model m2)^"\n");
    None)
  else
    let union _ v1 v2 =
      if v1.tag = v2.tag then Some v1 else None
    in
    Some
    { int_model = IM.union union m1.int_model m2.int_model;
      bool_model = IM.union union m1.bool_model m2.bool_model;
      vec_model = IM.union union m1.vec_model m2.vec_model; }

(* return a model containing mappings identical in both models *)
let model_inter m1 m2 =
  let inter _ v1 v2 =
    match (v1, v2) with
    | (Some v1, Some v2) ->
      if v1.tag = v2.tag then Some v1 else None
    | _ -> None
  in
  { int_model = IM.merge inter m1.int_model m2.int_model;
    bool_model = IM.merge inter m1.bool_model m2.bool_model;
    vec_model = IM.merge inter m1.vec_model m2.vec_model; }

(* return a model containing ITE'd mappings appearing in both models *)
let model_merge b m1 m2 =
  let merge _ v1 v2 =
    match (v1, v2) with
    | (Some v1, Some v2) ->
      Some (simpl (mk_ite b v1 v2))
    | _ -> None
  in
  { int_model = IM.merge merge m1.int_model m2.int_model;
    bool_model = IM.merge merge m1.bool_model m2.bool_model;
    vec_model = IM.merge merge m1.vec_model m2.vec_model; }

(* substituting values from models into symbolic expressions *)

(* accept a model assigning values to symbolic variables *)
(* substitute and simplify, memoizing intermediates *)
let subst' : type a. memo_tmap -> model -> a sym_value -> a sym_value =
  fun memo model v ->
  let rec do_subst : type a. a sym_value -> a sym_value =
    fun v ->
    match memo_tmap_mem memo v with
    | Some v -> v
    | None ->
      memo_tmap_add memo v
      (* if no vars to subst, skip *)
      begin match v.node with
      | SymInt i ->
        begin match IM.find_opt i model.int_model with
        | Some v -> v
        | None -> v
        end
      | SymBool i ->
        begin match IM.find_opt i model.bool_model with
        | Some v -> v
        | None -> v
        end
      | SymVec (i, _) ->
        begin match IM.find_opt i model.vec_model with
        | Some v -> v (* skipping length check *)
        | None -> v
        end
      | SymVal (IsInt, v) -> mk_int v
      | SymVal (IsBool, v) -> mk_bool v
      | SymVal (IsLoc l, v) -> mk_loc v l
      | SymVal (IsVec _, v) -> mk_vec v
      | SymVal (IsPtr l, (i, o)) ->
        let o = do_subst o in
        mk_ptr (i, o) l
      | SymVal (IsWord l, BitVec h) ->
        let h = do_subst h in
        mk_word (BitVec h) l
      | SymVal (IsWord l, BitPtr p) ->
        let p = do_subst p in
        mk_word (BitPtr p) l
      | SymIte (b, v1, v2) ->
        let b = do_subst b in
        let v1 = do_subst v1 in
        let v2 = do_subst v2 in
        simpl (mk_ite b v1 v2)
      | SymUnop (u, v) ->
        let v = do_subst v in
        simpl (mk_unop u v)
      | SymBinop (b, v1, v2) ->
        let v1 = do_subst v1 in
        let v2 = do_subst v2 in
        simpl (mk_binop b v1 v2)
      | SymMultiop (b, ls, t, k) ->
        let ls = List.map do_subst ls in
        simpl (mk_multiop b ls t k)
      | SymChoose (ls, tl) ->
        let subst_pair (b, v) = (do_subst b, do_subst v) in
        let ls = List.map subst_pair ls in
        let tl = do_subst tl in
        simpl (mk_choose ls tl)
      end
  in
  do_subst v

let subst : type a. model -> a sym_value -> a sym_value =
  fun model v ->
  let memo = mk_memo_tmap () in
  subst' memo model v

(* shrink a model to only involve variables in the given variable set *)
let model_project sv model =
  { int_model = IM.filter (fun k _ -> IS.mem k sv.int_set) model.int_model;
    bool_model = IM.filter (fun k _ -> IS.mem k sv.bool_set) model.bool_model;
    vec_model = IM.filter (fun k _ -> IM.mem k sv.vec_set) model.vec_model; }

(* completing incomplete models *)

(* add arbitrary value mappings to the model until
   all the vars in the given set are mapped *)
(* counter for getting arbitrary values *)
let complete_counter = ref 0
let model_complete sv model =
  let complete_int i m =
    if not (IM.mem i m) then
      let m = IM.add i (mk_int (bint_of_int !complete_counter)) m in
      complete_counter := !complete_counter + 1; m
    else
      m
  in
  let complete_bool i m =
    if not (IM.mem i m) then
      let m = IM.add i (mk_bool (!complete_counter mod 2 = 0)) m in
      complete_counter := !complete_counter + 1; m
      (*IM.add i (mk_bool true) m*)
    else
      m
  in
  let complete_vec i l m =
    if not (IM.mem i m) then
      let m = IM.add i (mk_vec (Bits.of_int l !complete_counter)) m in
      complete_counter := !complete_counter + 1; m
    else
      m
  in
  { int_model = IS.fold complete_int sv.int_set model.int_model;
    bool_model = IS.fold complete_bool sv.bool_set model.bool_model;
    vec_model = IM.fold complete_vec sv.vec_set model.vec_model }

(* generate the assertion that fixes variables to be the same as in a model *)
let assert_of_model model =
  let assert_of_int i v p =
    mk_binop LogAnd (mk_binop EqInt (mk_sym_int i) v) p
  in
  let assert_of_bool i v p =
    mk_binop LogAnd (mk_binop EqBool (mk_sym_bool i) v) p
  in
  let assert_of_vec i v p =
    mk_binop LogAnd (mk_binop EqVec (mk_sym_vec i (width_of_vec v)) v) p
  in
  simpl (mk_bool true
    |> IM.fold assert_of_int model.int_model
    |> IM.fold assert_of_bool model.bool_model
    |> IM.fold assert_of_vec model.vec_model)

(* get a model that refreshes variables in the given variable set *)
(* vars in the set are mapped to fresh variables of same type *)
let model_refresh vars =
  let refresh_ints i =
    IM.add i (next_sym_int ())
  in
  let refresh_bools i =
    IM.add i (next_sym_bool ())
  in
  let refresh_vecs i l =
    IM.add i (next_sym_vec l)
  in
  { int_model = IS.fold refresh_ints vars.int_set IM.empty;
    bool_model = IS.fold refresh_bools vars.bool_set IM.empty;
    vec_model = IM.fold refresh_vecs vars.vec_set IM.empty }
