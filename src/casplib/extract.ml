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
open Interpret

module A   = Casp_ast
module Pr  = Prettyast

let asm_translator casp ops (pos, (i, args)) =
  (* get the asm_stringtxt and its arguments *)
  let (prog_argls, asm_expr) =
    match List.assoc_opt i ops with
    | Some (p, a) -> (p, a)
    | None -> failat pos (i^" not found the format string")
  in
  (* arg (id * typ) list: get ID for each op arg *)
  let prog_argls = List.map fst prog_argls in
  (* (Pos.t, atomic) list: get atomic for each op *)
  let args = List.map snd args in
  (* (arg_id, atomic) pair *)
  let params = zip prog_argls args in
  let conf = CE.eval_config casp in
  let add_param (conf: CC.config) (i, a) =
    let v = CE.eval_atomic casp conf.env (pos, a) in
    { conf with top = SM.add i v conf.top;
                env = SM.add i v conf.env }
  in
  let conf = List.fold_left add_param conf params in
  match CE.eval_expr asm_expr conf with
  | Ok (ValStr s, _) -> s
  | Ok (v, _) -> failat pos ("string_expr: expected ValStr, but got "^(CC.string_of_value v))
  | Error (pos, s) -> failat pos ("string_expr: <error> "^(Pos.string_of pos)^": "^s)

(* proc_prog is typechecked derivative of prog_ast *)
(* casp_decls is the defop list used to typecheck proc_prog *)
let to_asm (casp: casp_file) (ext, prog) =
  (* update casp with extern labels *)
  let update_extern c (_, e) =
    { c with mems = SM.add ("mem_"^e) (c.wordsize, 1, c.wordsize, Some e) c.mems; lbls = SM.add e ("mem_"^e) c.lbls }
  in
  let casp = List.fold_left update_extern casp ext in
  (* defstr : (arg list * string_expr) SM.t *)
  let ops  = SM.bindings casp.defstr in
  let asms = List.map (asm_translator casp ops) prog in
  String.concat "\n" asms
