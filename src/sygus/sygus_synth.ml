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
open Symexec
open Query

open Sygus_transfer
open Sygus_protocol

type synth_result =
  | SynthSuccess of casp_inst list
  | SynthFailure

let do_synth spec max_insts =
  let transfer = transfer_init spec in
  if !settings.accumulation_direct ||
     !settings.accumulation_operation ||
     !settings.accumulation_category then
    protocol_run (init_accumulation transfer) max_insts
  else
    protocol_run (init_extend transfer) max_insts

let synth casp spec max_insts =
  let spec = spec |> eval_spec casp |> unify_spec in
  if !settings.debugging then begin
    print_log "SYNTH CALLED WITH SPEC:\n%s\n" (string_of_sspec spec);
    flush_log ()
  end;
  match snd (do_synth spec max_insts) with
  | ProtocolSuccess prog ->
    SynthSuccess prog
  | _ -> SynthFailure

let sketch casp spec sk =
  let spec = spec |> eval_spec casp |> unify_spec in
  let sp = prog_of_sketch casp sk in
  let transfer = transfer_init spec |> transfer_switch sp in
  match transfer_cegis [] transfer with
  | Ok prog -> SynthSuccess prog
  | Error (_, _) -> SynthFailure
