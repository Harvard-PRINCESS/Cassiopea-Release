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
open Smtlib

module U = Unix
module SU = Solver_util

type solver = SU.solver

let is_pool = false

let use_solver = ref "lingeling"

let solver i =
  let i = i mod 3 in
  if i = 0 then use_solver := "cadical"
  else if i = 1 then use_solver := "lingeling"
  else if i = 2 then use_solver := "minisat"

let create seed : solver =
  let cr, pw = U.pipe () in
  let pr, cw = U.pipe () in
  match U.fork () with
  | 0 ->
    (* we're the child: become the solver *)
    U.close pr;
    U.close pw;
    U.dup2 cr U.stdin;
    U.dup2 cw U.stdout;
    U.execvp "boolector" [| "boolector"; "--smt2"; "-SE"; !use_solver; "-uc"; "--normalize"; "--prop-nprops=10000"; "--prop-use-restarts"; "--prop-use-bandit" |]
  | pid ->
    (* we're the parent: drive the solver *)
    U.close cr;
    U.close cw;
    let from_sol = U.in_channel_of_descr pr in
    let to_sol = U.out_channel_of_descr pw in
    SU.print_ch to_sol
      ("(set-option :produce-models true)\n"^
       "(set-option :incremental 1)\n");
    begin match seed with
    | None -> ()
    | Some seed ->
      SU.print_ch to_sol
        ("(set-option :seed "^
        (string_of_int seed)^")\n")
    end;
    { pid = pid;
      from_sol = from_sol;
      to_sol = to_sol;
      asserts = ref SS.empty;
      sol_env = ref env_empty;
      stack = ref []; }

let create_with_solver seed i : solver =
  let _ = solver i in
  create seed


let to_string = SU.to_string
let assert_ = SU.assert_
let clear _ = failwith "boolector does not support reset"
let close = SU.close
let push = SU.push
let pop = SU.pop

(* strip either BTOR_[num]@ or BTOR@[num] from front of var name *)
let strip_btor_exp = Str.regexp
  ( "BTOR[^@]*@[0-9]*"^
    "\\([A-Za-z_][a-zA-Z0-9_]*\\)" )

let strip_btor model =
  let strip (i, a) =
    (* print_string ((Str.replace_first strip_btor_exp "\\1" i)^"\n"); *)
    (Str.replace_first strip_btor_exp "\\1" i, a)
  in
  List.map strip model

let check = SU.check (fun from_sol -> Smtlib_lex.read_next from_sol |> strip_btor)
