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

(* maps, sets, and memoization utilities for symbolic values *)

(* map and set type definitions *)

module SVM = Map.Make(struct
  type t=sym_ex_t
  let compare x1 x2 = compare x1.tag x2.tag
end)
module SVS = Set.Make(struct
  type t=sym_ex_t
  let compare x1 x2 = compare x1.tag x2.tag
end)

module SBS = Set.Make(struct
  type t = bool sym_value
  let compare v1 v2 = compare v1.tag v2.tag
end)

(* maps from values to values -- maintaining separate maps per type index *)
type vmap = {
  int_map : bint sym_value IM.t;
  bool_map : bool sym_value IM.t;
  loc_map : id sym_value IM.t;
  vec_map : bits sym_value IM.t;
  ptr_map : (id * bits sym_value) sym_value IM.t;
  word_map : word_t sym_value IM.t;
}

let vmap_empty = {
  int_map = IM.empty;
  bool_map = IM.empty;
  loc_map = IM.empty;
  vec_map = IM.empty;
  ptr_map = IM.empty;
  word_map = IM.empty;
}

let vmap_add' :
  type a. vmap -> a sym_ref_t ->
    a sym_value -> a sym_value -> vmap =
  fun m t v1 v2 ->
  match t with
  | IsInt -> { m with int_map = IM.add v1.tag v2 m.int_map }
  | IsBool -> { m with bool_map = IM.add v1.tag v2 m.bool_map }
  | IsLoc _ -> { m with loc_map = IM.add v1.tag v2 m.loc_map }
  | IsVec _ -> { m with vec_map = IM.add v1.tag v2 m.vec_map }
  | IsPtr _ -> { m with ptr_map = IM.add v1.tag v2 m.ptr_map }
  | IsWord _ -> { m with word_map = IM.add v1.tag v2 m.word_map }

let vmap_add : type a. vmap -> a sym_value -> a sym_value -> vmap =
  fun m v1 v2 -> vmap_add' m (typ_of_sym_value v1) v1 v2

let vmap_mem' :
  type a. vmap -> a sym_ref_t ->
    a sym_value -> a sym_value option =
  fun m t v ->
  match t with
  | IsInt -> IM.find_opt v.tag m.int_map
  | IsBool -> IM.find_opt v.tag m.bool_map
  | IsLoc _ -> IM.find_opt v.tag m.loc_map
  | IsVec _ -> IM.find_opt v.tag m.vec_map
  | IsPtr _ -> IM.find_opt v.tag m.ptr_map
  | IsWord _ -> IM.find_opt v.tag m.word_map

let vmap_mem : type a. vmap -> a sym_value -> a sym_value option =
  fun m v -> vmap_mem' m (typ_of_sym_value v) v
