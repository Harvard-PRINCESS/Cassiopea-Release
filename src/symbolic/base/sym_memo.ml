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
open Sym_hash
open Sym_map

(* memoization utilities *)

(* weak map boilerplate *)
module IntWSM = Ephemeron.K1.Make(struct
  type t = bint sym_value
  let equal (v1 : t) (v2 : t) = v1.tag = v2.tag
  let hash (v : t) = v.tag
end)
module BoolWSM = Ephemeron.K1.Make(struct
  type t = bool sym_value
  let equal (v1 : t) (v2 : t) = v1.tag = v2.tag
  let hash (v : t) = v.tag
end)
module LocWSM = Ephemeron.K1.Make(struct
  type t = id sym_value
  let equal (v1 : t) (v2 : t) = v1.tag = v2.tag
  let hash (v : t) = v.tag
end)
module VecWSM = Ephemeron.K1.Make(struct
  type t = bits sym_value
  let equal (v1 : t) (v2 : t) = v1.tag = v2.tag
  let hash (v : t) = v.tag
end)
module PtrWSM = Ephemeron.K1.Make(struct
  type t = (id * bits sym_value) sym_value
  let equal (v1 : t) (v2 : t) = v1.tag = v2.tag
  let hash (v : t) = v.tag
end)
module WordWSM = Ephemeron.K1.Make(struct
  type t = word_t sym_value
  let equal (v1 : t) (v2 : t) = v1.tag = v2.tag
  let hash (v : t) = v.tag
end)

(* for 'a sym_value -> 'a sym_value *)
(* tmap = "type map" *)
type memo_tmap = {
  int_wtmap : bint sym_value IntWSM.t;
  bool_wtmap : bool sym_value BoolWSM.t;
  loc_wtmap : id sym_value LocWSM.t;
  vec_wtmap : bits sym_value VecWSM.t;
  ptr_wtmap : (id * bits sym_value) sym_value PtrWSM.t;
  word_wtmap : word_t sym_value WordWSM.t;
}

(* create a new memoization table *)
let mk_memo_tmap () = {
  int_wtmap = IntWSM.create 251;
  bool_wtmap = BoolWSM.create 251;
  loc_wtmap = LocWSM.create 251;
  vec_wtmap = VecWSM.create 251;
  ptr_wtmap = PtrWSM.create 251;
  word_wtmap = WordWSM.create 251;
}

(* check for a mapping *)
let memo_tmap_mem' :
  type a. memo_tmap ->
    a sym_ref_t ->
    a sym_value ->
    a sym_value option =
  fun memo t v ->
  match t with
  | IsInt -> IntWSM.find_opt memo.int_wtmap v
  | IsBool -> BoolWSM.find_opt memo.bool_wtmap v
  | IsLoc _ -> LocWSM.find_opt memo.loc_wtmap v
  | IsVec _ -> VecWSM.find_opt memo.vec_wtmap v
  | IsPtr _ -> PtrWSM.find_opt memo.ptr_wtmap v
  | IsWord _ -> WordWSM.find_opt memo.word_wtmap v

let memo_tmap_mem :
  type a. memo_tmap ->
    a sym_value ->
    a sym_value option =
  fun memo v ->
  memo_tmap_mem' memo (typ_of_sym_value v) v

let memo_tmap_add' :
  type a. memo_tmap ->
    a sym_ref_t ->
    a sym_value ->
    a sym_value ->
    a sym_value =
  fun memo t v v' ->
  match memo_tmap_mem' memo t v with
  | Some v'' ->
    if v'.tag <> v''.tag then
      failwith "memo_tmap_add: double add with different values!"
    else
      v'
  | None ->
  begin match t with
  | IsInt -> IntWSM.add memo.int_wtmap v v'
  | IsBool -> BoolWSM.add memo.bool_wtmap v v'
  | IsLoc _ -> LocWSM.add memo.loc_wtmap v v'
  | IsVec _ -> VecWSM.add memo.vec_wtmap v v'
  | IsPtr _ -> PtrWSM.add memo.ptr_wtmap v v'
  | IsWord _ -> WordWSM.add memo.word_wtmap v v'
  end; v'

(* remember a mapping; returns remembered value *)
let memo_tmap_add :
  type a. memo_tmap ->
    a sym_value ->
    a sym_value ->
    a sym_value =
  fun memo v v' ->
  memo_tmap_add' memo (typ_of_sym_value v) v v'

(* for 'a sym_value -> 'b *)
type 'b memo_map = {
  int_wmap : 'b IntWSM.t;
  bool_wmap : 'b BoolWSM.t;
  loc_wmap : 'b LocWSM.t;
  vec_wmap : 'b VecWSM.t;
  ptr_wmap : 'b PtrWSM.t;
  word_wmap : 'b WordWSM.t;
}

(* create a new memoization table *)
let mk_memo_map () = {
  int_wmap = IntWSM.create 251;
  bool_wmap = BoolWSM.create 251;
  loc_wmap = LocWSM.create 251;
  vec_wmap = VecWSM.create 251;
  ptr_wmap = PtrWSM.create 251;
  word_wmap = WordWSM.create 251;
}

let memo_map_mem : type a b. b memo_map -> a sym_value -> b option =
  fun memo v ->
  match typ_of_sym_value v with
  | IsInt -> IntWSM.find_opt memo.int_wmap v
  | IsBool -> BoolWSM.find_opt memo.bool_wmap v
  | IsLoc _ -> LocWSM.find_opt memo.loc_wmap v
  | IsVec _ -> VecWSM.find_opt memo.vec_wmap v
  | IsPtr _ -> PtrWSM.find_opt memo.ptr_wmap v
  | IsWord _ -> WordWSM.find_opt memo.word_wmap v

let memo_map_add : type a b. b memo_map -> a sym_value -> b -> b =
  fun memo v v' ->
  begin match typ_of_sym_value v with
  | IsInt -> IntWSM.add memo.int_wmap v v'
  | IsBool -> BoolWSM.add memo.bool_wmap v v'
  | IsLoc _ -> LocWSM.add memo.loc_wmap v v'
  | IsVec _ -> VecWSM.add memo.vec_wmap v v'
  | IsPtr _ -> PtrWSM.add memo.ptr_wmap v v'
  | IsWord _ -> WordWSM.add memo.word_wmap v v'
  end; v'

(* for checking if 'a sym_value has been seen *)
type memo_set = SVS.t ref

let mk_memo_set () = ref SVS.empty

let memo_set_add memo v =
  memo := SVS.add (ex_of_sym_value v) !memo; v

let memo_set_mem memo v =
  SVS.mem (ex_of_sym_value v) !memo
