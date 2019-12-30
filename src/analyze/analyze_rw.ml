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

open Analyze_util

module RWV = Rw_value
module RWC = Config(Rw_value)
module RWE = Eval(RWV)(RWC)

(* read-/write-set analysis *)

(* to use: given an ea_term (e.g. from apply_spec), you can constrain
   a program based on its analyzed read/write sets by using this code
   snippet:

  let (rs, ws) = analyze_rw casp sp in
  let rw_assert = assert_of_rw casp spec.access spec.modify rs ws in
  let term = { term with asserts = SV.log_and term.asserts rw_assert } in*)

(* generate a map from register names to bv representations
   given a set of register names, e.g.
   R0 -> 0b0000000000000001,
   R1 -> 0b0000000000000010,
   R2 -> 0b0000000000000100 *)
let regmap_of_regs regs =
  let sz = SM.cardinal regs in
  let add_reg reg _ (cur, map) =
    (Bits.lshift cur BI.one, SM.add reg cur map)
  in
  snd (SM.fold add_reg regs (Bits.of_big_int sz BI.one, SM.empty))

let string_of_regmap regmap =
  let string_of_pair (n, b) = n^" : "^(Bits.to_hexstring b) in
  String.concat "\n" (List.map string_of_pair (SM.bindings regmap))

(* generate a bitvector representation of a register string set given
   a generated register-to-bv map *)
let bv_of_set regmap regset =
  let bv_of_set' reg bv =
    match SM.find_opt reg regmap with
    | Some v -> Bits.or_ v bv
    | None -> failwith ("bv_of_set: register "^reg^" not found")
  in
  SS.fold bv_of_set' regset (Bits.zero 16)

let init_rw_conf (c : casp) : RWC.config =
  let mk_reg l = (SS.empty, l) in
  let mk_mem (l, n, r, _) =
    let add_entry region o =
      let o = Bits.of_int r (o * 4) in
      BM.add o SS.empty region
    in
    (l, n, List.fold_left add_entry BM.empty (range 0 n))
  in
  { c = c;
    top = RWE.eval_env c;
    env = RWE.eval_env c;
    reg = SM.map mk_reg c.regs;
    mem = SM.map mk_mem c.mems;
    ctx = RWV.ctx_init;
    jmp = RWV.lift_int BI.zero_big_int; }

let analyze_rw_inst (conf : RWC.config) (pos, (i, aa)) =
  let vv = List.map (RWE.eval_atomic conf.c conf.top) aa in
  RWE.eval_op pos i vv conf

let analyze_rs c regmap =
  let conf = init_rw_conf c in
  let analyze_rs' i vv =
    match analyze_rw_inst conf (Pos.none, (i, vv)) with
    | Ok conf -> mk_vec (bv_of_set regmap conf.ctx.rd)
    | Error _ -> mk_vec (bv_of_set regmap SS.empty)
  in
  lift_analyze analyze_rs'

let analyze_ws c regmap =
  let conf = init_rw_conf c in
  let analyze_ws' i vv =
    match analyze_rw_inst conf (Pos.none, (i, vv)) with
    | Ok conf -> mk_vec (bv_of_set regmap conf.ctx.wt)
    | Error _ -> mk_vec (bv_of_set regmap SS.empty)
  in
  lift_analyze analyze_ws'

let analyze_rw_sym_inst (c : casp_file) sp =
  let regmap = regmap_of_regs c.regs in
  (* print_string ("RegMap:\n"^(string_of_regmap regmap)^"\n"); *)
  let rs = List.map (analyze_sym_inst (analyze_rs c regmap)) sp in
  let ws = List.map (analyze_sym_inst (analyze_ws c regmap)) sp in
  (* print_string ("ReadSet List: "^(String.concat "\n" (List.map string_of_sym_value rs))^"\n");
  print_string ("WriteSet List: "^(String.concat "\n" (List.map string_of_sym_value ws))^"\n\n"); *)
  (rs, ws)

let assert_of_rw (c: casp_file) _access modify _rs ws =
  let regmap = regmap_of_regs c.regs in
  (*let access = bv_of_set regmap access in*)
  let modify = bv_of_set regmap modify in
  (*let rs = List.fold_left (mk_binop BitOr) (mk_vec (Bits.zero 16)) rs in*)
  let ws = List.fold_left (mk_binop BitOr) (mk_vec (Bits.zero 16)) ws in
  (* print_string ("Access List: "^(Bits.to_hexstring rs)^"\n");
  print_string ("Modify List: "^(Bits.to_hexstring ws)^"\n\n"); *)
  let rw = simpl (mk_binop EqVec ws (mk_binop BitAnd ws (mk_vec modify))) in
  (* print_string ("Write Constraint: "^(string_of_sym_value rw)^"\n"); *)
  rw
