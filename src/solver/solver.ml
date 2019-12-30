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

(* module for a connection to a solver *)
(* could be reimplemented for Z3, boolector, etc. *)
module type SolverType = sig
  (* maintain whatever info is needed here -- I presume some manner of channel *)
  (* any interaction state that needs saving will probably want to go here *)
  (* (in particular, it should at least keep an env, which assert adds to *)
  type solver

  (* output SMTLib text for testing *)
  val to_string : solver -> string

  (* initialize the solver *)
  (* creates a solver handle and pass init commands to the solver *)
  (* after this, the solver process should be ready to:
     - run incrementally
     - generate models for queries *)
  val create : int option -> solver

  (* add an assertion to current solver state *)
  (* this adjusts an internally maintained environment
     and a list of booleans that will be asserted come solve time *)
  (* likely uses Smtlib.encode *)
  val assert_ : solver -> bool sym_value -> unit

  (* push a stack frame onto the solver,
     outputting stored declarations and assertions *)
  val push : solver -> unit
  val pop : solver -> unit

  (* spit the environment at the solver and assert what's needed *)
  (* then come back with the solution, mapping symbolic variables to
    what the solver says is a satisfying assignment *)
  (* None: unsat *)
  (* Some sol: satisfying assignment to symbolic variables *)
  val check : solver -> model option

  (* clear the solver state, as for another round of interaction *)
  val clear : solver -> unit

  (* close out solver, free resources *)
  val close : solver -> unit
end

(* solvers we support *)
module Z3Solver : SolverType = Z3_solver
module BoolectorSolver : SolverType = Boolector_solver
module YicesSolver : SolverType = Yices_solver
module PoolSolver : SolverType = Pool_solver
module YicesPoolSolver : SolverType = Yices_pool_solver

type solver =
| Z3S of Z3Solver.solver
| BtorS of BoolectorSolver.solver
| YicesS of YicesSolver.solver
| PoolS of PoolSolver.solver
| YicesPoolS of YicesPoolSolver.solver

type solver_t =
| Z3
| Btor
| Yices
| Pool
| YicesPool

(* dispatchers *)

let string_of_solver =
  function
  | Z3S s -> Z3Solver.to_string s
  | BtorS s -> BoolectorSolver.to_string s
  | YicesS s -> YicesSolver.to_string s
  | PoolS s -> PoolSolver.to_string s
  | YicesPoolS s -> YicesPoolSolver.to_string s

let solver_create' t =
  let seed =
    if !settings.seed <> 0 then
      Some (!settings.seed)
    else
      None
  in
  match t with
  | Z3 -> Z3S (Z3Solver.create seed)
  | Btor -> BtorS (BoolectorSolver.create seed)
  | Yices -> YicesS (YicesSolver.create seed)
  | Pool -> PoolS (PoolSolver.create seed)
  | YicesPool -> YicesPoolS (YicesPoolSolver.create seed)

let solver_create =
  function
  | "z3" -> solver_create' Z3
  | "btor" -> solver_create' Btor
  | "yices" -> solver_create' Yices
  | "pool" -> solver_create' Pool
  | "yicespool" -> solver_create' YicesPool
  | s -> failwith ("unrecognized solver name: "^s)

let solver_assert s v =
  match s with
  | Z3S s -> Z3Solver.assert_ s v
  | BtorS s -> BoolectorSolver.assert_ s v
  | YicesS s -> YicesSolver.assert_ s v
  | PoolS s -> PoolSolver.assert_ s v
  | YicesPoolS s -> YicesPoolSolver.assert_ s v

let solver_push s =
  match s with
  | Z3S s -> Z3Solver.push s
  | BtorS s -> BoolectorSolver.push s
  | YicesS s -> YicesSolver.push s
  | PoolS s -> PoolSolver.push s
  | YicesPoolS s -> YicesPoolSolver.push s

let solver_pop s =
  match s with
  | Z3S s -> Z3Solver.pop s
  | BtorS s -> BoolectorSolver.pop s
  | YicesS s -> YicesSolver.pop s
  | PoolS s -> PoolSolver.pop s
  | YicesPoolS s -> YicesPoolSolver.pop s

let solver_check s =
  match s with
  | Z3S s -> Z3Solver.check s
  | BtorS s -> BoolectorSolver.check s
  | YicesS s -> YicesSolver.check s
  | PoolS s -> PoolSolver.check s
  | YicesPoolS s -> YicesPoolSolver.check s

let solver_clear s =
  match s with
  | Z3S s -> Z3Solver.clear s
  | BtorS s -> BoolectorSolver.clear s
  | YicesS s -> YicesSolver.clear s
  | PoolS s -> PoolSolver.clear s
  | YicesPoolS s -> YicesPoolSolver.clear s

let solver_close s =
  match s with
  | Z3S s -> Z3Solver.close s
  | BtorS s -> BoolectorSolver.close s
  | YicesS s -> YicesSolver.close s
  | PoolS s -> PoolSolver.close s
  | YicesPoolS s -> YicesPoolSolver.close s

