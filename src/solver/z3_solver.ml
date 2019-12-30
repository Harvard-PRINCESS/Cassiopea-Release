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
    U.execvp "z3" [| "z3"; "-smt2"; "-in" |]
  | pid ->
    (* we're the parent: drive the solver *)
    U.close cr;
    U.close cw;
    let from_sol = U.in_channel_of_descr pr in
    let to_sol = U.out_channel_of_descr pw in
    SU.print_ch to_sol
      ("(set-option :interactive-mode true)\n"^
       "(set-option :model-evaluator.completion true)\n");
    begin match seed with
    | None -> ()
    | Some seed ->
      SU.print_ch to_sol
        ("(set-option :random-seed "^
        (string_of_int seed)^")\n")
    end;
    { pid = pid;
      from_sol = from_sol;
      to_sol = to_sol;
      asserts = ref SS.empty;
      sol_env = ref env_empty;
      stack = ref []; }

let to_string = SU.to_string
let assert_ = SU.assert_
let clear = SU.clear
let close = SU.close
let push = SU.push
let pop = SU.pop
let check = SU.check (fun from_sol -> Smtlib_lex.read_next from_sol)
