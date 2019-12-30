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
open Query

open Deduce_goal
open Deduce_plan

(* deduction rules for deductive synthesis *)

(* deduction rules accept a one-hole context and return applicable subplans *)

(* deref an as-yet-unread pointer in a register *)
let synth_deref ((goal, _) : path) =
  match find_unloaded_ptr goal with
  (* no pointer to read *)
  | None -> []
  (* deref contents of register i to get value (v, l) *)
  | Some (i, (v, l)) ->
    (* mark dereferenced register *)
    let goal = { goal with deref_regs = SS.add i goal.deref_regs } in

    (* demand the dereferenced value *)
    let (fresh, goal) = add_fresh_reg l goal in
    let (goal1, goal2) = demand_reg fresh (v, l) goal in

    let goal1 = relevant_reg (SS.of_list [i; fresh]) goal1 in

    [plan_of_rule (RuleDeref i) goal1 goal2]

(* load an as-yet-unread value in memory *)
let synth_load ((goal, _) : path) =
  (* TODO for now, we pattern match precond for unread pointers to memory *)
  (* better: determine a DEPENDENCE on some unread precond memory contents *)
  match find_unloaded_mem goal with
  (* no location to load *)
  | None -> []
  (* load location (i, o) to get value (v, l) *)
  | Some ((i, o), (v, l)) ->
    (* mark loaded value *)
    let loaded_mems = SM.add i
      (match SM.find_opt i goal.loaded_mems with
      | Some m -> BS.add o m
      | None -> BS.add o BS.empty)
      goal.loaded_mems
    in
    let goal = { goal with loaded_mems = loaded_mems } in

    (* demand the value in this location *)
    let (fresh, goal) = add_fresh_reg l goal in
    let (goal1, goal2) = demand_reg fresh (v, l) goal in

    [plan_of_rule (RuleLoad (i, o)) goal1 goal2]

(* TODO move a value from one register to another *)
(* smarter register allocation might make that a rename *)

(* fix the value in a register *)
let synth_fixreg ((goal, _) : path) =
  match find_unsat_reg goal with
  | None -> []
  | Some (i, (v, l)) ->
    let (goal1, goal2) = demand_reg i (v, l) goal in
    let goal1 = { goal1 with moving_regs = SS.add i goal.moving_regs } in

    [plan_of_rule (RuleMove i) goal1 goal2]

(* fix the value in a memory location *)
let synth_fixmem ((goal, _) : path) =
  match find_unsat_mem goal with
  | None -> []
  | Some ((i, o), v) ->
    let (goal1, goal2) = demand_mem (i, o) v goal in
    let moving_mems = SM.add i
      (match SM.find_opt i goal.moving_mems with
      | Some m -> BS.add o m
      | None -> BS.add o BS.empty)
      goal.moving_mems
    in
    let goal1 = { goal1 with moving_mems = moving_mems } in

    [plan_of_rule (RuleWrite (i, o)) goal1 goal2]

(* under load and fixmem, first find the pointer to write *)
let synth_findptr ((goal, path) : path) =
  match path with
  | Left (RuleLoad (i, o), _, _)
  | Left (RuleWrite (i, o), _, _) ->
    (* create pointer to this location *)
    let r =
      match SM.find_opt i (get_casp goal).mems with
      | Some (_, _, r, _) -> r
      | None -> failwith "deduce: synth_load: invalid pointer?!"
    in
    let ptr = mk_word (BitPtr (mk_ptr (i, mk_vec o) r)) r in

    (* demand a pointer to this location *)
    let (fresh, goal) = add_fresh_reg r goal in
    let (goal1, goal2) = demand_reg fresh (ptr, r) goal in

    [plan_of_rule (RuleMove fresh) goal1 goal2]
  | _ -> []

(* given a context, generate list of applicable plans *)
let synthesize path : plan' list =
  [ (*synth_deref;*)
    synth_load;
    synth_fixreg;
    synth_fixmem;
    synth_findptr; ]
  |> List.map (fun rule -> rule path)
  |> List.concat
