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
open Symexec
open SI

(* addition in log space *)
let logadd x y =
  if x < y then
    x +. log1p (exp ((y -. x) *. log 2.)) /. log 2.
  else
    y +. log1p (exp ((x -. y) *. log 2.)) /. log 2.

let bitsize_of_vars _vars = 1.
  (*if vars_is_empty vars then 1.
  else
    float_of_int ((IS.cardinal vars.int_set) * 32 +
    (IS.cardinal vars.bool_set) +
    (IM.fold (fun _ l sz -> sz + l) vars.vec_set 0))*)

let rec bitsize_of_disjoint : type a. a sym_value -> float =
  fun v ->
  match v.node with
  | SymIte (_, v1, v2) ->
    let sz1 = bitsize_of_disjoint v1 in
    let sz2 = bitsize_of_disjoint v2 in
    logadd sz1 sz2
  | SymChoose (ls, tl) ->
    List.map (fun (_, v) -> bitsize_of_disjoint v) ls
    |> List.fold_left logadd (bitsize_of_disjoint tl)
  | _ ->
    bitsize_of_vars (vars_of_sym_value v)

let bitsize_of_value =
  function
  | ValInt v -> bitsize_of_vars (vars_of_sym_value v)
  | ValBool v -> bitsize_of_vars (vars_of_sym_value v)
  | ValWord (v, _) ->
    begin match v.node with
    | SymVal (IsWord _, BitVec v) ->
      bitsize_of_vars (vars_of_sym_value v)
    | _ -> bitsize_of_disjoint v
    end
  | ValLoc (v, _) -> bitsize_of_disjoint v
  | ValStr _ -> 0.

let rec bitsize_of_sym_inst =
  function
  | ConInst (_, args) ->
    List.map bitsize_of_value args
    |> List.fold_left (+.) 0.0
  | SymInstIte (_, i1, i2) ->
    let sz1 = bitsize_of_sym_inst i1 in
    let sz2 = bitsize_of_sym_inst i2 in
    logadd sz1 sz2
