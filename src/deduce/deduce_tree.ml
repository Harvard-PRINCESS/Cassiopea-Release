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
open Sygus

open Deduce_goal
open Deduce_plan
open Deduce_rules

(* using synthesis plans for synthesis *)

let rec prog_of_plan (_, plan) =
  match plan with
  | PlanCegis _ ->
    failwith "prog_of_plan: plan still has a hole!"
  | PlanDone prog -> prog
  | PlanRule (_, plan1, plan2) ->
    (prog_of_plan plan1) @ (prog_of_plan plan2)

(* straightforward DFS plan search *)
(* only attempts CEGIS on 1-instruction holes *)
let rec dfs_deduce' plan : plan option =
  (* short-circuiting failure when unsat postcond detected *)
  if pred_implies (get_post (fst plan)) (mk_bool false) then
    None
  else match path_of_plan plan with
  (* no more holes: done *)
  | None -> Some plan
  (* found a hole: try 1-instruction CEGIS *)
  | Some (state, path) ->
    if !settings.debugging then begin
      print_log "SMT %s\n"
        (string_of_int (fst state));
      flush_log ()
    end;
    match protocol_run state 1 with
    | (_, ProtocolSuccess prog) ->
      (* fill hole and move to next *)
      dfs_deduce' (path_fill (PlanDone prog) path)
    | _ ->
      (* attempt to deduce subgoals *)
      let try_plans plan plan' =
        match plan with
        (* we've already succeeded *)
        | Some plan -> Some plan
        (* plug in next plan to try *)
        | None -> dfs_deduce' (path_fill plan' path)
      in
      List.fold_left try_plans None (synthesize path)

let dfs_deduce goal : plan option =
  dfs_deduce' (plan_of_goal goal)

(* cost-guided deductive search *)
(* attempt least expensive plans in terms of estimated SMT cost *)

(* cost based on SMT holes *)
let rec cost_of_plan' (_, plan) : int =
  match plan with
  | PlanCegis (i, _) ->
    if i = 0 then 100
    else if i = 1 then 1000
    else if i = 2 then 10000
    else 100000
  | PlanDone _ -> 0
    (*let i = List.length prog in
    if i = 1 then -5
    else if i = 2 then -50
    else if i = 3 then -500
    else -5000*)
  | PlanRule (_, plan1, plan2) ->
    (cost_of_plan' plan1) + (cost_of_plan' plan2)

(* reweight based on plan depth *)
let cost_of_plan plan : int =
  match path_of_plan plan with
  | None -> -10000000
  | Some (_, _path) ->
    (*-(depth_of_path path) * 100 +*) (cost_of_plan' plan)

let heap_add_plan plan heap =
  let cost = cost_of_plan plan in
  if !settings.debugging then begin
    print_log "ADDING PLAN:\n%s\nCOST:%s\n"
      (string_of_plan plan)
      (string_of_int cost);
    flush_log ()
  end;
  match IM.find_opt cost heap with
  | None -> IM.add cost [plan] heap
  | Some ls -> IM.add cost (plan :: ls) heap

let rec min_deduce' heap : plan option =
  match IM.min_binding_opt heap with
  | None -> None
  | Some (cost, []) ->
    min_deduce' (IM.remove cost heap)
  | Some (cost, plan :: rest) ->
    if !settings.synth_verbose then begin
      print_log "MIN PLAN:\n%s\nCOST: %s\n"
        (string_of_plan plan)
        (string_of_int cost);
      flush_log ()
    end;
    let heap = IM.add cost rest heap in
    begin match path_of_plan plan with
    (* no more holes: done *)
    | None -> Some plan
    (* found a hole: attempt synthesis *)
    | Some (state, path) ->
      (* stop after 1 on the first run; otherwise stop after next *)
      let insts = fst state in
      let max_insts = if insts = 0 then 1 else insts in
      let plans =
        match protocol_run state max_insts with
        | (_, ProtocolSuccess prog) ->
          [PlanDone prog]
        | (insts, ProtocolContinue state) ->
          if insts = 2 then
            (* first-time CEGIS: apply rules *)
            PlanCegis (2, state) :: synthesize path
          else
            (* just keep going *)
            [PlanCegis (insts, state)]
      in
      (List.fold_left
        (fun heap plan -> heap_add_plan (path_fill plan path) heap)
        heap plans)
      |> min_deduce'
    end

let min_deduce goal : plan option =
  let plan = plan_of_goal goal in
  min_deduce' (heap_add_plan plan IM.empty)
