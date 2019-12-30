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

(* break down symbolic arguments for analyses that require concrete insts *)
(* symbolic values are instantiated arbitrarily *)
(* results of analysis on each branch are gathered under ITEs *)
(* note that this takes time in the product of the arg ITE sizes *)
let lift_analyze eval_one (inst : id) (vv: value list) =
  let rec peel_symval: type a. a sym_value -> (Pos.t * atomic) list -> value list -> _ =
    fun arg vals ls ->
    (* XXX args cannot contain operations *)
    match arg.node with
    | SymVal (IsInt, i) -> peel_arg (vals @ [(Pos.none, Int i)]) ls
    | SymVal (IsBool, b) -> peel_arg (vals @ [(Pos.none, Bool b)]) ls
    | SymVal (IsLoc _, l) -> peel_arg (vals @ [(Pos.none, Id l)]) ls
    | SymVal (IsVec _, v) -> peel_arg (vals @ [(Pos.none, Vec v)]) ls
    | SymVal (IsPtr _, p) ->
      let (i, o) = p in
      begin match o.node with
      | SymVal (IsInt, o) -> peel_arg (vals @ [(Pos.none, Ptr (i, o))]) ls
      | SymInt _ -> peel_arg (vals @ [(Pos.none, Ptr (i, BI.zero_big_int))]) ls
      | SymIte (b, i1, i2) ->
        mk_ite b (peel_symval i1 vals ls) (peel_symval i2 vals ls)
      | _ -> failwith "one_inst_rw: should have IsInt here"
      end
    | SymVal (IsWord _, w) ->
      begin match w with
      | BitVec v -> peel_symval v vals ls
      | BitPtr p -> peel_symval p vals ls
      end
    | SymVec (_, len) -> peel_arg (vals @ [(Pos.none, Vec (Bits.zero len))]) ls
    | SymIte (b, i1, i2) ->
      mk_ite b (peel_symval i1 vals ls) (peel_symval i2 vals ls)
    | _ -> failwith "analyze_inst: unknown type for symbolic instruction"
  and peel_arg (vals : (Pos.t * atomic) list) (svals : value list) =
    match svals with
    | i :: vs ->
      begin match i with
      | ValInt v -> peel_symval v vals vs
      | ValBool v -> peel_symval v vals vs
      | ValLoc (v, _) -> peel_symval v vals vs
      | ValWord (v, _) -> peel_symval v vals vs
      | ValStr s -> peel_arg (vals @ [(Pos.none, Str s)]) vs
      end
    | [] -> eval_one inst vals
  in
  peel_arg [] vv

let rec analyze_sym_inst analyze (si: inst) =
  match si with
  | ConInst (i, vv) -> analyze i vv
  | SymInstIte (b, si1, si2) ->
    let res1 = analyze_sym_inst analyze si1 in
    let res2 = analyze_sym_inst analyze si2 in
    mk_ite b res1 res2
