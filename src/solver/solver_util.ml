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
open Symvars
open Smtlib

module SA = Smtlib_ast
module S  = Smtlib
module P  = Printf
module U  = Unix

type solver = {
  pid : int; (* pid of solver process *)

  from_sol : in_channel;  (* pipe from the solver *)
  to_sol : out_channel;   (* pipe to the solver *)

  (* assertions are remembered by variable names *)
  asserts : SS.t ref; (* current assertions*)
  sol_env : env ref;  (* current environment*)

  (* environment/assertion stack *)
  stack : (SS.t * env) list ref;
}

let print_ch ch s =
  if !settings.dump_solver then begin
    Printf.fprintf !settings.smt_ch "%s" s;
    flush !settings.smt_ch;
  end;
  Printf.fprintf ch "%s" s;
  flush ch

let string_of_asserts asserts =
  asserts |> SS.elements
  |> List.map (fun v -> "(assert "^v^")")
  |> String.concat "\n"

(* encode new stack frame *)
let encode_frame (s : solver) =
  (* produce only the new declarations *)
  match !(s.stack) with
  | [] ->
    let asserts_str = string_of_asserts !(s.asserts) in
    let sol_env_str = string_of_env !(s.sol_env) in
    sol_env_str^"\n"^asserts_str
  | (old_asserts, old_sol_env) :: _ ->
    let new_asserts = SS.diff !(s.asserts) old_asserts in
    let asserts_str = string_of_asserts new_asserts in
    let sol_env_str = string_of_env_new !(s.sol_env) old_sol_env in
    sol_env_str^"\n"^asserts_str

(* dump out the effective environment and assertion list *)
let to_string (s : solver) =
  let string_of_frame (asserts, sol_env) =
    let asserts_str = string_of_asserts asserts in
    let sol_env_str = string_of_env sol_env in
    "env: "^sol_env_str^"\nasserts: "^asserts_str
  in
  (!(s.asserts), !(s.sol_env)) :: !(s.stack)
  |> List.map string_of_frame
  |> String.concat "\n\n"

let assert_ (s : solver) (sv : bool sym_value) =
  let (v, env) = encode sv !(s.sol_env) in
  let asserts = SS.add v !(s.asserts) in
  s.asserts := asserts;
  s.sol_env := env

let push (s : solver) =
  (* push a stack frame, including stored assertions and declarations *)
  print_ch s.to_sol ((encode_frame s)^"\n(push 1)\n");
  (* record push in environment stack with a new head environment *)
  s.stack := (!(s.asserts), !(s.sol_env)) :: !(s.stack)

let pop (s : solver) =
  (* pop the top assertion set from the stack*)
  let _ = print_ch s.to_sol "(pop 1)\n" in
  match !(s.stack) with
  | [] -> failwith "attempted to pop empty solver stack"
  | (old_asserts, old_sol_env) :: stack ->
    (s.asserts := old_asserts;
    s.sol_env := old_sol_env;
    s.stack := stack)

let clear (s : solver) =
  print_ch s.to_sol "(reset)\n";
  s.asserts := SS.empty;
  s.sol_env := env_empty;
  s.stack := []

let close (s : solver) =
  print_ch s.to_sol "(exit)\n";
  close_in s.from_sol;
  close_out s.to_sol;
  let _ = U.wait () in ()

(* get the result back *)
let rec get_result smt_read (s : solver) =
  let res = input_line s.from_sol in
  if !settings.dump_solver then begin
    print_log "CHECK LINE: %s\n" res;
    flush_log ()
  end;

  if res = "sat" then begin
    (* if solver returns sat, get a model *)
    print_ch s.to_sol "(get-model)\n";
    let o = smt_read s.from_sol in
    try
      Some (decode o !(s.sol_env))
    with _ ->
      failwith "failure in smtlib decode"
  end else if res = "unsat" then
    (* if solver returns unsat, signal unsat *)
    None
  else if res = "" then begin
    (* skip blank lines: wtf? *)
    print_string "blank line\n";
    get_result smt_read s
  end else if res = "unsupported" then
    failwith "solver_check: fed solver unsupported config directive"
  else
    failwith ("solver_check: got bad check-sat response: "^res)

(* NOTE: always push before applying check *)
(*let check (smt_read : in_channel -> (id * smtlib_ast.atom) list) (s : solver) =*)
let check smt_read (s : solver) =
  print_ch s.to_sol ("(check-sat)\n");
  get_result smt_read s
