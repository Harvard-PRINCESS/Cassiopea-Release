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

module A = Arg
module S = Sys

(* represent actions to be performed *)
type command =
| Interp  (* input prog, input start state, output, dump *)
| Verify  (* input spec, input prog, dump *)
| Synth   (* input spec, output, dump *)
| Sketch  (* input spec, input sketch_prog, output, dump *)
| Deduce  (* input spec, output, dump *)
| Extract (* input prog, output, dump *)
| Bitsize

let string_of_command = function
  | Interp -> "Interp"
  | Verify -> "Verify"
  | Synth -> "Synth"
  | Sketch -> "Sketch"
  | Deduce -> "Deduce"
  | Extract -> "Extract"
  | Bitsize -> "Bitsize"

let cmd:   command option ref = ref None
let files: string list ref    = ref []

let outfile:      string ref  = ref ""
let logfile:      string ref  = ref ""
let smtfile:      string ref  = ref ""

let synth_verbose: bool ref   = ref false
let debugging:    bool ref    = ref false
let dump_interp:  bool ref    = ref false
let dump_solver:  bool ref    = ref false

let dry_run:      bool ref    = ref false
let max_insts:    int ref     = ref 4
let bucket:       bool ref    = ref false
let accumulation_direct:    bool ref    = ref false
let accumulation_operation: bool ref    = ref false
let accumulation_category:  bool ref    = ref false
let sorting:      bool ref    = ref false
let weak_coerce:  bool ref    = ref false
let no_unify:     bool ref    = ref false
let no_depend:   bool ref    = ref false
let no_branch:    bool ref    = ref false

let cex_solver:   string ref  = ref "z3"
let syn_solver:   string ref  = ref "btor"

let seed:         int ref     = ref 0
let whiten:       string list ref = ref []

let string_of_command_args () =
  let cmd =
    match (!cmd, !files) with
    (* command with good args *)
    | (Some Interp, [_; prog; init]) ->
      P.sprintf "Interpret prog %s with start state %s" prog init
    | (Some Verify, [_; spec; prog]) ->
      P.sprintf "Verify prog %s against spec %s" prog spec
    | (Some Synth, [_; spec]) ->
      P.sprintf "Synthesize for spec %s" spec
    | (Some Sketch, [_; spec; sketch]) ->
      P.sprintf "Synthesize for spec %s with sketch %s" spec sketch
    | (Some Deduce, [_; spec]) ->
      P.sprintf "Synthesize for spec %s" spec
    | (Some Extract, [_; prog]) ->
      P.sprintf "Extract ASM from prog %s" prog
    | (Some Bitsize, [_]) ->
      P.sprintf "Show bitsize"
    (* wrong arg counts *)
    | (Some c, _) ->
      P.sprintf "%s got wrong number of args: [%s]"
                (string_of_command c)
                (String.concat ";" !files)
    (* no command *)
    | (None, _) ->
      P.sprintf "No command given. Args: [%s]" (String.concat "\n" !files)
  in
  let out_name =
    if !outfile = "" then "<stdout>"
    else !outfile
  in
  let log_name =
    if !logfile = "" then "<stdout>"
    else !logfile
  in
  let file =
    P.sprintf "output to %s; log to %s" out_name log_name
  in
  cmd ^ " " ^ file

let opts = [
  (* command flags *)
  ("-interp", A.Unit (fun () -> cmd := Some Interp),
          "[prog] [init]: interpret [prog] on starting state [init]");
  ("-verify", A.Unit (fun () -> cmd := Some Verify),
          "[spec] [prog]: verify [prog] against [spec]");
  ("-synth", A.Unit (fun () -> cmd := Some Synth),
          "[spec]: synthesize prog from [spec]");
  ("-sketch", A.Unit (fun () -> cmd := Some Sketch),
          "[spec] [sketch]: synthesize prog from [spec] with [sketch]");
  ("-deduce", A.Unit (fun () -> cmd := Some Deduce),
          "[spec] : synthesize prog from [spec]");
  ("-extract", A.Unit (fun () -> cmd := Some Extract),
          "[prog] : extract ASM from [prog]");
  ("-bitsize", A.Unit (fun () -> cmd := Some Bitsize),
          ": show approximate per-instruction search space size");

  (* file flags *)
  ("-o", A.Set_string outfile, ": set file for result output");
  ("-l", A.Set_string logfile, ": set file for logging");
  ("-smt", A.Set_string smtfile, ": set file for smtlib dump");

  (* output flags *)
  ("-sv", A.Set synth_verbose, ": print synthesis details");
  ("--debug", A.Set debugging, ": enable debug logging mode");
  ("--dump-interp", A.Set dump_interp, ": dump interpreter function calls");
  ("--dump-solver", A.Set dump_solver, ": dump solver interaction");

  (* synthesis flags *)
  ("--dry-run", A.Set dry_run, ": cause CEGIS to always fail");
  ("--max-insts", A.Set_int max_insts, ": maximum instructions (default 4)");
  ("--bucketed", A.Set bucket, ": synthesis with counter-example bucketing");
  ("--accumulation-direct", A.Set accumulation_direct, ": synthesis with fine-grained candidate accumulation, ");
  ("--accumulation-operation", A.Set accumulation_operation, ": synthesis with coarse-grained candidate accumulation, at operation level");
  ("--accumulation-category", A.Set accumulation_category, ": synthesis with coarse-grained candidate accumulation, at category level");
  ("--sorting", A.Set sorting, ": synthesis with assembly instruction sorting");
  ("--weak-coerce", A.Set weak_coerce, ": use weaker coercion");
  ("--no-unify", A.Set no_unify, ": disable equality unification for specifications");
  ("--no-depend", A.Set no_depend, ": disable dependency assertions");
  ("--no-branch", A.Set no_branch, ": disable branching");

  (* solver flags *)
  ("--use-cex-solver", A.Set_string cex_solver, ": set verification solver (z3, btor, yices) (z3 by default)");
  ("--use-syn-solver", A.Set_string syn_solver, ": set synthesis solver (z3, btor, yices) (btor by default)");

  (* randomization *)
  ("--seed", A.Set_int seed, ": set random seed for whitening and SMT solver");
  ("--whiten", A.String (arl whiten), ": whiten [solver, logic, insts, args]");
]

let usage = [
  "Usage: " ++ Batteries.exe ++ " [command] casp [files...] [options...]";
  "       [command] := -interp | -verify | -synth | -sketch | -deduce |-extract";
  "";
  "Cassiopeia accepts a command indicating what action it should perform.";
  "A command might expect some files. The accepted file types are as follows:";
  " * prog : files containing a list of instructions";
  " * spec : files containing pre-/post-condition specs";
  "The following describes flags and possible commands with their expected arguments:"]
  |> String.concat "\n"

let parse_args () =
  (* options description is in "opts" *)
  (* extraneous things are expected to be files and handled
     by sticking them onto the files list *)
  A.parse opts (arl files) usage
