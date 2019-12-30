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
open Casp_ast
open Sygus

module PA = Prettyast

open Deduce_goal

(* type for deduction rules *)
type rule =
  | RuleDeref of id       (* dereference a register's contents *)
  | RuleLoad of id * bits  (* load a memory location *)
  | RuleMove of id        (* fix value in a register *)
  | RuleWrite of id * bits (* fix value in a memory location *)

(* type for synthesis plans *)
type plan' =
  | PlanCegis of prot_state         (* apply CEGIS to complete goal *)
  | PlanDone of casp_inst list      (* goal completed with program *)
  | PlanRule of rule * plan * plan  (* apply a deduction rule *)
and plan = goal * plan'

(* one-hole contexts for synthesis plans *)
type path' =
  | Top
  | Left of rule * plan * path
  | Right of plan * rule * path
and path = goal * path'

let string_of_rule =
  function
  | RuleDeref i -> "DEREF "^i
  | RuleLoad (i, o) -> "LOAD "^i^" "^(string_of_int (Bits.to_int o))
  | RuleMove i -> "MOVE "^i
  | RuleWrite (i, o) -> "WRITE "^i^" "^(string_of_int (Bits.to_int o))

let string_of_plan plan =
  let rec make_string prefix (_, plan) =
    match plan with
    | PlanCegis (insts, _) ->
      prefix ^ "CEGIS " ^ string_of_int (if insts = 0 then 1 else insts)
    | PlanDone prog ->
      prefix ^ "DONE " ^
      (prog
      |> List.map PA.string_of_inst
      |> String.concat " ")
    | PlanRule (rule, plan1, plan2) ->
      prefix ^ (string_of_rule rule) ^ "\n" ^
      (make_string ("| "^prefix) plan1) ^ "\n" ^
      (make_string ("| "^prefix) plan2)
  in
  make_string "" plan

let rec string_of_path (_, path) =
  match path with
  | Top -> "TOP"
  | Left (rule, _, path) ->
    "LEFT "^(string_of_rule rule)^" "^(string_of_path path)
  | Right (_, rule, path) ->
    "RIGHT "^(string_of_rule rule)^" "^(string_of_path path)

let rec depth_of_path (_, path) =
  match path with
  | Top -> 0
  | Left (_, _, path) ->
    1 + depth_of_path path
  | Right (_, _, path) ->
    1 + depth_of_path path

let plan_of_goal (goal : goal) =
  let transfer = transfer_init goal.spec in
  if !settings.accumulation_direct ||
     !settings.accumulation_operation ||
     !settings.accumulation_category then
    (goal, PlanCegis (init_accumulation transfer))
  else
    (goal, PlanCegis (init_extend transfer))

let plan_of_rule rule goal1 goal2 =
  PlanRule (rule, plan_of_goal goal1, plan_of_goal goal2)

(* fill current context with given plan' *)
let rec path_fill plan' (goal, path) : plan =
  match path with
  | Top -> (goal, plan')
  | Left (rule, plan, path') ->
    path_fill (PlanRule (rule, (goal, plan'), plan)) path'
  | Right (plan, rule, path') ->
    path_fill (PlanRule (rule, plan, (goal, plan'))) path'

(* return path to first PlanSmt in plan tree *)
(* also return the associated CEGIS state *)
let path_of_plan (goal, plan) : (prot_state * path) option =
  let rec make_path (goal, plan) path =
    match plan with
    | PlanCegis state -> Some (state, (goal, path))
    | PlanDone _ -> None
    | PlanRule (rule, plan1, plan2) ->
      begin match make_path plan1 (Left (rule, plan2, (goal, path))) with
      | Some path -> Some path
      | None ->
        begin match make_path plan2 (Right (plan1, rule, (goal, path))) with
        | Some path -> Some path
        | None -> None
        end
      end
  in
  make_path (goal, plan) Top
