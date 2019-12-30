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



open Ast

let print'ty ty =
   match ty with
   | BOOL -> "bool"
   | INT -> "Z"
   | BV -> "nat"

let fix_varname x =
   let fixchar c =
      match c with
      | '$' -> '_'
      | '.' -> '_'
      | _ -> c
   in
   String.map fixchar x

let print'name x ty =
   fix_varname x ^ ": " ^ print'ty ty

let rec print'expr e =
   let apply op args =
      let args' = List.map print'expr args in
      "(" ^ op ^ " " ^ String.concat " " args' ^ ")"
   in
   match e with
   | CONST (_, _, BOOL) -> Util.crash "boolean integer constant"
   | CONST (_, k, INT) -> string_of_int k ^ "%Z"
   | CONST (_, k, BV) -> string_of_int k
   | READVAR (_, x, _) -> fix_varname x
   | IF (_, c, t, f) ->
        let c' = print'expr c in
        let t' = print'expr t in
        let f' = print'expr f in
        "(if " ^ c' ^ " then " ^ t' ^ " else " ^ f' ^ ")"
   | SLICE (pos, e1, a, b) ->
        apply "nat_bitslice" [e1; CONST (pos, a, BV); CONST (pos, b, BV)]
   | BV2INT (_, e1) -> apply "Z.of_nat" [e1]
   | BOOLOP (_, op, args) ->
        let op' = match op with
           | LOGNOT -> "negb"
           | LOGAND -> "andb"
           | LOGOR -> "orb"
           | LOGEQ -> "eqb"
        in
        apply op' args
   | INTOP (_, op, args) ->
        let op' = match op with
           | INTEQ -> "Z.eqb"
           | INTLT -> "Z.ltb"
           | INTADD -> "Z.add"
           | INTSUB -> "Z.sub"
        in
        apply op' args
   | BVOP (_, op, args) ->
        let op' = match op with
           | BVEQ -> "Nat.eqb"
           | BVLT -> "Nat.ltb"
           | BVADD -> "Nat.add"
           | BVSUB -> "Nat.sub"
           | BVUSHR -> "Nat.shiftr"
           | BVSHL -> "Nat.shiftl"
           | BVBITAND -> "nat_bitand"
           | BVBITOR -> "nat_bitor"
        in
        apply op' args

let print'stmt seen s =
   let checkdef () =
      if !seen = false then begin
         seen := true;
         "Definition stuff :=\n"
      end else ""
   in

   match s with
   | ASSERT (_, e) ->
        checkdef () ^
        print'expr e ^ "."
   | DECL (_, x, ty) ->
        "Variable " ^ print'name x ty ^ "."
   | LET (_, x, ty, e) ->
        checkdef () ^
        "let " ^ print'name x ty ^ " := " ^ print'expr e ^ " in "
   | MISC (_, txt) -> "(* " ^ txt ^ " *)"

let header =
   "Require Import Bool.\n" ^
   "Require Import Arith ZArith Omega.\n" ^
   "\n" ^
   "Definition nat_bitslice: nat -> nat -> nat -> nat. Admitted.\n" ^
   "Definition nat_bitand: nat -> nat -> nat. Admitted.\n" ^
   "Definition nat_bitor: nat -> nat -> nat. Admitted.\n" ^
   "\n" ^
   "Ltac clean :=\n" ^
   "   repeat (\n" ^
   "      try rewrite Z.add_0_r;\n" ^
   "      try rewrite Z.eqb_refl;\n" ^
   "      try rewrite Nat.eqb_refl;\n" ^
   "      try rewrite andb_true_r;\n" ^
   "      try rewrite orb_true_r;\n" ^
   "      try rewrite andb_false_r;\n" ^
   "      try rewrite orb_false_r;\n" ^
   "      try rewrite andb_true_l;\n" ^
   "      try rewrite orb_true_l;\n" ^
   "      try rewrite andb_false_l;\n" ^
   "      try rewrite orb_false_l;\n" ^
   "      try rewrite andb_diag;\n" ^
   "      try rewrite orb_diag;\n" ^
   "      simpl).\n" ^
   "\n" ^
   "Ltac logic :=\n" ^
   "   repeat (\n" ^
   "      try rewrite andb_true_iff;\n" ^
   "      try rewrite andb_false_iff;\n" ^
   "      try rewrite orb_true_iff;\n" ^
   "      try rewrite orb_false_iff;\n" ^
   "      try rewrite negb_true_iff;\n" ^
   "      try rewrite negb_false_iff).\n" ^
   "\n" ^
   "Section Stuff.\n" ^
   "\n"

let footer =
   "\n" ^
   "End Stuff.\n" ^
   "\n"

let go stmts =
   let ctx = ref false in
   header ^
   (String.concat "\n" (List.map (print'stmt ctx) stmts)) ^ "\n" ^
   footer
