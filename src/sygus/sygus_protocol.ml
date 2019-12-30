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

(* extend a transfer function with a fresh instruction *)
let do_extend transfer =
  (* TODO select single instruction extensions appropriately:
      - do not read uninitialized values
      - do not write to any possible value *)
  let inst =
    if !settings.sorting then
      next_sort_sym_inst transfer.spec.casp sort_func_order firstorder
    else
      next_sym_inst transfer.spec.casp
  in
  transfer_extend inst transfer

(* state for protocols we support *)
type prot_state' =
  | ExtendState of transfer
  | AccumulationState of transfer * transfer list
and prot_state = int * prot_state'

(* results of protocol runs *)
type prot_result' =
  | ProtocolSuccess of casp_inst list
  | ProtocolContinue of prot_state'
and prot_result = int * prot_result'

(* size-extension synthesis *)
let protocol_extend _ transfer =
  match transfer_cegis [] transfer with
  (* report success *)
  | Ok prog -> ProtocolSuccess prog
  (* try again with longer length *)
  | Error (_, _) -> ProtocolContinue (ExtendState (do_extend transfer))

(* prefix accumulation synthesis *)
let protocol_accumulation insts (transfer, prefixes) =
  (* convert last candidate into a prefix *)
  let prefix_of_cands transfer cands =
    (* adjust subst_method to change prefix extraction behavior *)
    (* for concrete program: subst_prog *)
    (* for concrete program abstracted by instruction: abstract_prog *)
    (* for concrete program abstracted by category: category_prog cegis.spec.casp *)
    match cands with
    | last :: _ ->
      let subst_method =
        if !settings.accumulation_direct then
          subst_prog
        else if !settings.accumulation_category then
          category_prog transfer.spec.casp
        (* default is accumulation_operation *)
        else abstract_prog
      in
      [transfer_switch (subst_method last transfer.sp) transfer]
    | [] -> []
  in

  (* try a saved prefix *)
  let try_prefix' prefix =
    let prefix_insts = List.length prefix.sp in

    if !settings.synth_verbose then begin
      print_log "\tExtending %s-inst candidate to %s insts:\n\n"
        (string_of_int prefix_insts) (string_of_int insts) ;
      print_log "\tTrying prefix accumulation:\n\n";
      flush_log ()
    end;

    (* extend saved prefix to current length *)
    let extend_one prefix i =
      transfer_extend (List.nth transfer.sp i) prefix
    in
    let extended =
      range prefix_insts insts
      |> List.fold_left extend_one prefix
    in

    (* attempt synthesis *)
    match transfer_cegis [] extended with
    (* success: return program model *)
    | Ok prog -> Ok prog
    (* failure: return next things to try *)
    | Error (_, cands) ->
      if !settings.synth_verbose then begin
        print_log "\t%s-prefix candidate synth failed\n"
          (string_of_int prefix_insts);
        flush_log ()
      end;
      Error (prefix_of_cands transfer cands)
  in

  (* foldable version *)
  let try_prefix status prefix =
    match status with
    (* already succeeded: continue *)
    | Ok prog -> Ok prog
    (* accumulate new prefixes *)
    | Error prefixes ->
      match try_prefix' prefix with
      | Ok prog -> Ok prog
      | Error prefixes' ->
        Error (prefixes @ prefixes')
  in

  if !settings.synth_verbose then begin
    print_log "\tAccumulation: %s insts, %s prefixes\n"
      (string_of_int insts)
      (string_of_int (List.length prefixes));
    flush_log ()
  end;

  (* first, try accumulated prefixes *)
  match List.fold_left try_prefix (Error []) prefixes with
  | Ok prog ->
    if !settings.synth_verbose then begin
      print_log "\tAccumulation synth succeeded!\n";
      flush_log ()
    end;
    ProtocolSuccess prog

  | Error prefixes ->
    (* second, try fresh program *)
    if !settings.synth_verbose then begin
      begin if List.length prefixes = 0 then
        print_log "\tNo prefixes, trying fresh program\n"
      else
        print_log "\tAccumulation synth failed, trying fresh program\n"
      end;
      flush_log ()
    end;

    match transfer_cegis [] transfer with
    (* success: return *)
    | Ok prog -> ProtocolSuccess prog
    (* failure: add last failed candidate to prefixes *)
    | Error (_, cands) ->
      let fresh =
        if insts = 0 then []
        else prefix_of_cands transfer cands
      in
      let transfer = do_extend transfer in
      let prefixes = fresh @ prefixes in
      ProtocolContinue (AccumulationState (transfer, prefixes))

let init_extend transfer =
  let insts = List.length transfer.sp in
  (insts, ExtendState transfer)

let init_accumulation transfer =
  let insts = List.length transfer.sp in
  (insts, AccumulationState (transfer, []))

let protocol_step insts =
  function
  | ExtendState transfer ->
    protocol_extend insts transfer
  | AccumulationState (transfer, prefixes) ->
    protocol_accumulation insts (transfer, prefixes)

(* run a protocol up to max_insts insts *)
let rec protocol_run (insts, state) max_insts =
  if insts <= max_insts then
    (* run one step *)
    match protocol_step insts state with
    | ProtocolSuccess prog -> (insts, ProtocolSuccess prog)
    | ProtocolContinue state ->
      protocol_run (insts + 1, state) max_insts
  else
    (* do nothing *)
    (insts, ProtocolContinue state)
