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

(* utilities for deductive search state manipulation *)

type goal = {
  (* search state metadata *)
  deref_regs : SS.t;        (* registers w/ already-dereferenced pointers *)
  loaded_mems : BS.t SM.t;  (* memory locs we've already tried to load *)
  moving_regs : SS.t;
  moving_mems : BS.t SM.t;

  (* specification *)
  spec : sspec;
}

let get_casp (goal : goal) = goal.spec.casp
let get_pre (goal : goal) = goal.spec.pre
let get_post (goal : goal) = goal.spec.post
let set_casp (goal : goal) casp =
  { goal with spec = { goal.spec with casp = casp } }
let set_pre (goal : goal) pre =
  { goal with spec = { goal.spec with pre = pre } }
let set_post (goal : goal) post =
  { goal with spec = { goal.spec with post = post } }

(* create a fresh register and add it to the machine description *)
let reg_count = ref 0
let add_fresh_reg l (goal : goal) =
  reg_count := !reg_count + 1;
  let fresh = "FRESH_"^(string_of_int !reg_count) in
  let casp = get_casp goal in
  let goal = set_casp goal
    { casp with regs = SM.add fresh l casp.regs }
  in
  (fresh, goal)

(* find a register that makes f return Some *)
let find_reg f reg =
  let find i (v, l) = function
    | Some x -> Some x
    | None -> f i (v, l)
  in
  SM.fold find reg None

(* find a memory location that makes f return Some *)
let find_mem f mem =
  let find_region i (l, n, m) =
    let find o v = function
      | Some x -> Some x
      | None -> f i l n o v
    in
    function
    | Some x -> Some x
    | None -> BM.fold find m None
  in
  SM.fold find_region mem None

(* find a pointer whose value is not in a register *)
let find_unloaded_ptr (goal : goal) =
  let unloaded_ptr i (v, _) =
    if SS.mem i goal.deref_regs then
      (* don't try to read an already-read register *)
      None
    else
      (* see if this reg contains a pointer *)
      match v.node with
      | SymVal (IsWord _, BitVec _) -> None
      | SymVal (IsWord _, BitPtr p) ->
        (* assuming memory regions contain wordsize only *)
        (* get the pointer's value *)
        let wordsize = (get_casp goal).wordsize in
        begin match fetch p wordsize (get_pre goal).mem ctx_init with
        | Error _ -> None
        | Ok (v, _) ->
          (* loading a pointer might fail on some branches: should handle ctx *)
          (* see if this pointer's value is in a register *)
          let eq_to_load _ (v', l') =
            if l' <> wordsize then
              false
            else
              pred_implies (get_pre goal) (eq_word v v')
          in
          if SM.exists eq_to_load (get_pre goal).reg then
            None
          else
            Some (i, (v, wordsize))
        end
      | SymIte (_, _, _) -> None
      | _ -> failwith "deduce: synth_deref: invalid word?!"
  in
  find_reg unloaded_ptr (get_pre goal).reg

let find_unloaded_mem (goal : goal) =
  (* find a memory location whose value is not in a register *)
  let unloaded_mem i l _ o v =
    (* don't try to load an already-loaded location *)
    let was_loaded =
      match SM.find_opt i goal.loaded_mems with
      | Some loaded_set -> BS.mem o loaded_set
      | None -> false
    in
    if was_loaded then
      None
    else
      (* see if this value is already in a register *)
      let eq_value _ (v', l') =
        if l <> l' then
          false
        else
          pred_implies (get_pre goal) (eq_word v v')
      in
      if SM.exists eq_value (get_pre goal).reg then
        None
      else
        Some ((i, o), (v, l))
  in
  find_mem unloaded_mem (get_pre goal).mem

(* find a register such that:
   - its value in postcond is avars-only
   - its value in postcond does not match its value in precond *)
let find_unsat_reg (goal : goal) =
  let avars = avars_of_spec goal.spec in
  let unsat_reg i (v, l) =
    if SS.mem i goal.moving_regs then
      (* don't try to move a reg we're already trying to move *)
      None
    else if vars_is_empty (vars_diff (vars_of_sym_value v) avars) then
      (* only try to move avars-only regs *)
      begin match SM.find_opt i (get_pre goal).reg with
      | None -> Some (i, (v, l)) (* unspecified in precond *)
      | Some (v', _) ->
        if pred_implies (get_pre goal) (eq_word v v') then
          None
        else
          Some (i, (v, l)) (* not equal to value in precond *)
      end
    else None
  in
  find_reg unsat_reg (get_post goal).reg

(* find a memory location whose value in postcond does not match value in precond *)
let find_unsat_mem (goal : goal) =
  let avars = avars_of_spec goal.spec in
  let unsat_mem i _ _ o v =
    let is_moving =
      match SM.find_opt i goal.moving_mems with
      | Some moving_set -> BS.mem o moving_set
      | None -> false
    in
    if is_moving then
      None
    else if vars_is_empty (vars_diff (vars_of_sym_value v) avars) then
      (* only try to write avars-only mems *)
      match SM.find_opt i (get_pre goal).mem with
      | None -> Some ((i, o), v) (* unspecified in precond *)
      | Some (_, _, m) ->
        begin match BM.find_opt o m with
        | None -> Some ((i, o), v) (* unspecified in precond *)
        | Some v' ->
          if pred_implies (get_pre goal) (eq_word v v') then
            None
          else
            Some ((i, o), v) (* not equal to value in precond *)
        end
    else None
  in
  find_mem unsat_mem (get_post goal).mem

(* split a goal across a register set *)
(* goal 1 demands that register i be set to value v *)
(* goal 2 attempts to meet the original postcondition *)
let demand_reg i (v, l) (goal : goal) =
  (* intermediate specification: old precond plus new register value *)
  let pred = { (get_pre goal) with reg = SM.add i (v, l) (get_pre goal).reg } in
  let goal1 = set_post goal pred in
  let goal2 = set_pre goal pred in

  (goal1, goal2)

(* split a goal across a memory set *)
(* goal 1 demands that location (i, o) be set to value v *)
(* goal 2 attempts to meet the original postcondition *)
let demand_mem (i, o) v (goal : goal) =
  let region = match SM.find_opt i (get_pre goal).mem with
    | Some (l, n, m) -> (l, n, BM.add o v m)
    | None ->
      begin match SM.find_opt i (get_post goal).mem with
      | Some (l, n, _) -> (l, n, BM.singleton o v)
      | None -> failwith ("demand_mem: region "^i^" does not exist in post?!")
      end
  in

  (* intermediate specification: old precond plus new memory location value *)
  let pred = { (get_pre goal) with mem = SM.add i region (get_pre goal).mem } in
  let goal1 = set_post goal pred in
  let goal2 = set_pre goal pred in

  (goal1, goal2)

(* project a goal down to specified set of registers *)
(* TODO can't do this until we know to leave flags in frame *)
let relevant_reg _regset goal = goal
