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

open Monad
open Value
open Config
open Eval
open Inst

(* executing programs *)

module Exec = functor
  (V : Value)
  (C : module type of Config(V))
  (I : Inst with type config = C.config) ->
struct
  open V
  open C
  open I

  type trace = {
    (* current pc *)
    pc : int;
    (* starting state *)
    init : config;
    (* ending states at each pc *)
    finals : (config, Pos.t * string) result IM.t;
  }

  let trace_init conf = {
    pc = 0;
    init = conf;
    finals = IM.empty;
  }

  let string_of_trace {pc; init; finals} =
    "INIT:\n"^(string_of_config init)^"\n"^
    (IM.bindings finals
    |> List.map (fun (pc, conf) ->
      "AT "^(string_of_int pc)^":\n"^
      match conf with
      | Ok conf -> (string_of_config conf)
      | Error (pos, s) -> "error: "^(Pos.string_of pos)^": "^s)
    |> String.concat "\n")^
    "CURRENT PC: "^(string_of_int pc)

  let trace_next_straight {pc; init; finals} =
    if pc = 0 then
      Ok init
    else match IM.find_opt (pc - 1) finals with
    | Some conf -> conf
    | None -> failwith "trace_next: missing previous config!"

  (* get initial state for next pc *)
  (* TODO make this single fold *)
  let trace_next {pc; init; finals} =
    (* generating initial state for the next instruction *)
    (* merge previous finals that jump to the current pc *)
    let dst = lift_int (bint_of_int pc) in
    let gather next (_src, prev) =
      match (next, prev) with
      | (Ok next, Ok prev) ->
        let b = eq_int prev.jmp dst in
        Ok (conf_merge b prev next)
      | (Error e, Ok prev) ->
        let b = eq_int prev.jmp dst in
        begin match V.assert_ "" b prev.ctx with
        | Ok ((), ctx) -> Ok { prev with ctx = ctx }
        | Error _ -> Error e
        end
      | (Ok next, Error _) -> Ok next
      | (Error _, Error e) -> Error e
    in
    let init =
      if pc = 0 then
        Ok init
      else
        Error (Pos.none, "unreachable")
    in
    IM.bindings finals
    |> List.rev
    |> List.fold_left gather init

  let trace_next =
    if !settings.no_branch then
      trace_next_straight
    else
      trace_next

  (* execute single instruction *)
  let exec_inst inst ({pc; init; finals} as trace) =
    let final =
      match trace_next trace with
      | Ok conf ->
        let nextpc = lift_int (bint_of_int (pc + 1)) in
        eval_inst inst { conf with jmp = nextpc }
      | Error (pos, s) -> Error (pos, s)
    in
    { pc = pc + 1;
      init = init;
      finals = IM.add pc final finals; }

  (* execute a program with branching *)
  (* returns a trace: get the next state with trace_next *)
  let exec_prog' prog trace =
    let exec trace inst = exec_inst inst trace in
    List.fold_left exec trace prog

  let exec_prog prog conf =
    trace_next (exec_prog' prog (trace_init conf))
end

module CI = Concrete_inst.Make(CV)(CC)(CE)
module CX = Exec(CV)(CC)(CI)

module SI = Symbolic_inst
module SX = Exec(SV)(SC)(SI)
