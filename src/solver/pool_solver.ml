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

module U  = Unix
module SU = Solver_util
module P  = Printf
module ST = Boolector_solver

type solver = {
  seed : int option;
  solvers : SU.solver list ref;

  (* assertions are remembered by variable names *)
  asserts : SS.t ref; (* current assertions*)
  sol_env : env ref;  (* current environment*)

  (* environment/assertion stack *)
  stack : (SS.t * env) list ref;
}

let num_solvers = 3
let sigkill     = 9

let create_n n seed =
  let seed_one seed i =
    match seed with
    | None -> None
    | Some seed -> Some (seed * (n+1) + i*n)
  in
  range 0 n |> List.map (fun i -> ST.create_with_solver (seed_one seed i) i)

let create seed =
  { seed = seed;
    solvers = ref (create_n num_solvers seed);
    asserts = ref SS.empty;
    sol_env = ref env_empty;
    stack = ref []; }

let to_string (_s: solver) =
  failwith "to_string not allowed on pool solvers"

let assert_ (s: solver) (sv: bool sym_value) = 
  let (v, env) = encode sv !(s.sol_env) in
  let asserts = SS.add v !(s.asserts) in
  s.asserts := asserts;
  s.sol_env := env

let push (s: solver) = 
  List.iter ST.push !(s.solvers);
  s.stack := (!(s.asserts), !(s.sol_env)) :: !(s.stack)

let pop (s: solver) =
  match !(s.stack) with
  | [] -> failwith "attempted to pop empty solver stack"
  | (old_asserts, old_sol_env) :: stack ->
    (List.iter ST.pop !(s.solvers);
    s.asserts := old_asserts;
    s.sol_env := old_sol_env;
    s.stack := stack)

let close (s: solver) =
  List.iter ST.close !(s.solvers)

(* set one solver checking *)
let check_sat (s: ST.solver) =
  SU.print_ch s.to_sol "(check-sat)\n"

(* set all solvers checking *)
let checkall (s: solver) =
  List.iter check_sat !(s.solvers)

let kill (s : ST.solver) =
  U.kill s.pid sigkill;
  let _ = U.wait () in ()

(* kill all solvers *)
let killall (s: solver) =
  List.iter kill !(s.solvers)

let restore asserts sol_env stack (s: ST.solver) =
  (* yeet a frame onto the solver *)
  let push_one asserts sol_env =
    s.asserts := asserts;
    s.sol_env := sol_env;
    ST.push s
  in
  (* push all the old frames onto the solvers *)
  List.fold_right (fun (a, e) _ -> push_one a e) stack ();
  (* restore current frame *)
  s.asserts := asserts;
  s.sol_env := sol_env

let restoreall (s: solver) =
  List.iter (restore !(s.asserts) !(s.sol_env) !(s.stack)) !(s.solvers)

(* recreate solvers *)
let recreate (s: solver) =
  (* kill everyone *)
  killall s;
  (* boot n new solvers *)
  s.solvers := create_n num_solvers s.seed;
  (* replace each solver's stack *)
  restoreall s

(* get first finishing solver *)
let wait_on_first solvers =
  let descr_of_solver (s : ST.solver) =
    U.descr_of_in_channel s.from_sol
  in
  let fds = List.map descr_of_solver solvers in
  let fd = ref U.stdin in
  let _ = while !fd = U.stdin do
    let (rd, _, _) = U.select fds [] [] (0.01) in
      if List.length rd > 0 then
      fd := List.hd rd
    done in
  List.find (fun s -> !fd = descr_of_solver s) solvers

let get_model (s : ST.solver) =
  (* NOTE configured for ST = Boolector_solver *)
  let smt_read from_sol =
    Smtlib_lex.read_next from_sol |> ST.strip_btor
  in
  SU.get_result smt_read s

(* NOTE: always push before applying check *)
let check (s : solver) =
  (* print check commands *)
  checkall s;
  (* get first finishing solver *)
  let first = wait_on_first !(s.solvers) in
  let model = get_model first in
  recreate s; model

let clear (s: solver) =
  s.asserts := SS.empty;
  s.sol_env := env_empty;
  s.stack := [];
  recreate s
