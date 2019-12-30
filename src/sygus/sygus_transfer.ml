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

open Sygus_depend

(* incremental transfer functions *)

type transfer = {
  spec : sspec;
  sp : SI.inst list;
  trace : trace;
}

(* initialize transfer function for a spec *)
let transfer_init spec =
  let init = config_of_pred spec.casp spec.pre in
  { spec = spec; sp = []; trace = trace_init init; }

(* set sp for this transfer function *)
let transfer_switch sp' {spec; sp; trace} =
  let _ = sp in
  let trace = exec_prog' sp' (trace_init trace.init) in
  { spec = spec; sp = sp'; trace = trace; }

(* extend current trace with one instruction (saving some work) *)
(* update final config with single instruction eval *)
let transfer_extend inst {spec; sp; trace} =
  { spec = spec;
    sp = sp @ [inst];
    trace = exec_inst inst trace; }

(* attempt CEGIS with current symbolic program *)
let transfer_cegis cexs {spec; sp; trace} =
  print_log "Synthesis with %s insts starting\n"
    (string_of_int (List.length sp));
  flush_log ();

  if !settings.debugging then begin
    print_log "CEGIS ON SPEC:\n%s\n" (string_of_sspec spec);
    flush_log ()
  end;

  match trace_next trace with
  (* program fails: bail out *)
  | Error (pos, s) ->
    print_log "Symbolic program always fails!\nAt %s: %s\n"
      (Pos.string_of pos) s;
    flush_log ();
    Error ([], [])

  (* program succeeds: synthesize *)
  | Ok final ->
    let term =
      apply_spec spec sp trace.init final
      |> add_depends spec final
    in

    (* model printing function for guesses *)
    let model_printer cand =
      if !settings.synth_verbose then begin
        let prog_string = sp
          |> subst_prog cand
          |> lower_prog spec.casp
          |> List.map PA.string_of_inst
          |> String.concat "\n"
        in
        print_log "%s\n" prog_string;
        flush_log ()
      end
    in

    (* run easolve *)
    let sol =
      if !settings.dry_run then
        (None, ([], []))
      else
        easolve model_printer cexs term
    in

    match sol with
    (* solution found; output a program *)
    | (Some model, _) ->
      let prog = subst_prog model sp
        |> lower_prog spec.casp
      in
      Ok prog

    (* no solution found; output counterexamples *)
    | (None, (cexs, cands)) ->
      print_log "Synthesis with %s insts failed with %s candidates, %s counterexamples!\n"
        (string_of_int (List.length sp))
        (string_of_int (List.length cands))
        (string_of_int (List.length cexs));
      if !settings.debugging then begin
        print_log "With counterexamples:\n%s\n\n"
          (cexs
          |> List.map (fun m -> subst_config m trace.init)
          |> List.map string_of_config
          |> String.concat "\n")
      end;
      Error (cexs, cands)
