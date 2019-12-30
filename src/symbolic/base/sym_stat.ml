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

open Sym_ast
open Sym_hash
open Sym_memo

(* DAG statistics *)

(* how many distinct nodes are in the DAG rooted at v? *)
let rec size_of_sym_value' : type a. memo_set -> a sym_value -> int =
  fun memo v ->
  if memo_set_mem memo v then
    0
  else
    match (memo_set_add memo v).node with
    | SymVal (IsInt, _) -> 1
    | SymVal (IsBool, _) -> 1
    | SymVal (IsLoc _, _) -> 1
    | SymVal (IsVec _, _) -> 1
    | SymVal (IsPtr _, (_, o)) ->
      1 + size_of_sym_value' memo o
    | SymVal (IsWord _, BitVec h) ->
      1 + size_of_sym_value' memo h
    | SymVal (IsWord _, BitPtr p) ->
      1 + size_of_sym_value' memo p
    | SymInt _ -> 1
    | SymBool _ -> 1
    | SymVec _ -> 1
    | SymUnop (_, v) ->
      1 + size_of_sym_value' memo v
    | SymBinop (_, v1, v2) ->
      1 + size_of_sym_value' memo v1 + size_of_sym_value' memo v2
    | SymIte (b, v1, v2) ->
      1 + size_of_sym_value' memo b
        + size_of_sym_value' memo v1
        + size_of_sym_value' memo v2
    | SymMultiop (_, ls, _, _) ->
      List.fold_left
        (fun sz v -> 1 + sz + size_of_sym_value' memo v)
        1 (List.rev ls)
    | SymChoose (ls, tl) ->
      List.fold_left
        (fun sz (b, v) ->
          1 + sz + size_of_sym_value' memo b + size_of_sym_value' memo v)
        (size_of_sym_value' memo tl) (List.rev ls)

(* is there a faster algorithm? *)
let size_memo = mk_memo_map ()
let size_of_sym_value : type a. a sym_value -> int =
  fun v ->
  match memo_map_mem size_memo v with
  | Some sz -> sz
  | None ->
    let memo = mk_memo_set () in
    memo_map_add size_memo v (size_of_sym_value' memo v)

(* how long is the longest path to a leaf in the DAG rooted at v? *)
let depth_memo = mk_memo_map ()
let rec depth_of_sym_value : type a. a sym_value -> int =
  fun v ->
  match memo_map_mem depth_memo v with
  | Some v -> v
  | None ->
    memo_map_add depth_memo v
    begin match v.node with
    | SymVal (IsInt, _) -> 1
    | SymVal (IsBool, _) -> 1
    | SymVal (IsLoc _, _) -> 1
    | SymVal (IsVec _, _) -> 1
    | SymVal (IsPtr _, (_, o)) ->
      1 + depth_of_sym_value o
    | SymVal (IsWord _, BitVec h) ->
      1 + depth_of_sym_value h
    | SymVal (IsWord _, BitPtr p) ->
      1 + depth_of_sym_value p
    | SymInt _ -> 1
    | SymBool _ -> 1
    | SymVec _ -> 1
    | SymUnop (_, v) ->
      1 + depth_of_sym_value v
    | SymBinop (_, v1, v2) ->
      1 + max (depth_of_sym_value v1) (depth_of_sym_value v2)
    | SymIte (b, v1, v2) ->
      1 + max
        (depth_of_sym_value b)
        (max
          (depth_of_sym_value v1)
          (depth_of_sym_value v2))
    | SymMultiop (_, ls, _, _) ->
      List.fold_left
        (fun d v -> 1 + max (depth_of_sym_value v) d)
        1 (List.rev ls)
    | SymChoose (ls, tl) ->
      List.fold_left
        (fun d (b, v) -> 1 + max d (max
          (depth_of_sym_value b)
          (depth_of_sym_value v)))
        (depth_of_sym_value tl) (List.rev ls)
    end
