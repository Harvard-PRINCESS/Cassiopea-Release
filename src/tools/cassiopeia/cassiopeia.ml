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
open Interpret

module A = Arg
module S = Sys
module Opt = Options

let process_prog casp prog =
  (* parse program file *)
  let prog = Casp_lex.parse_with Casp_parse.prog_file prog in
  Process.process_prog casp prog

let process_sketch casp sketch =
  (* parse program file *)
  let sketch = Casp_lex.parse_with Casp_parse.sketch_file sketch in
  Process.process_sketch casp sketch

let process_init casp init =
  let init = Casp_lex.parse_with Casp_parse.init_file init in
  Process.process_init casp init

let process_spec casp spec =
  (* parse spec file *)
  let spec = Casp_lex.parse_with Casp_parse.spec_file spec in
  Process.process_spec casp spec

(* INTERP COMMAND *)
let interp casp prog init =
  (* prog eval *)
  let init_conf = CE.eval_config casp in
  let init_conf = CE.eval_start init init_conf in

  begin match CX.exec_prog prog init_conf with
  | Ok final_conf ->
    let _ = print_string "concrete execution succeeded\n" in
    print_out "Interp results:\n%s\n" (CC.string_of_config final_conf);
    begin if !settings.log_ch <> !settings.out_ch then
      print_log "Interp results:\n%s\n" (CC.string_of_config final_conf)
    end
  | Error (pos, s) ->
    failwith ("concrete execution failed at "^(Pos.string_of pos)^
              " with error: "^s)
  end;

  (* find register read/write sets *)
  let init_rw = Analyze_rw.RWE.eval_config casp in
  let get_rw inst =
    match Analyze_rw.analyze_rw_inst init_rw inst with
    | Ok conf -> conf.ctx
    | Error (pos, s) ->
      failwith ("read/write set analysis failed at "^(Pos.string_of pos)^
                " in instruction at "^(Pos.string_of (fst inst))^
                " with error: "^s)
  in
  let rw = List.map get_rw prog in
  print_log "Read/Write register sets for each instruction: \n%s\n"
    (String.concat "\n" (List.map Analyze_rw.RWV.ctx_to_string rw));
  0

(* VERIFICATION USING SYMBOLIC EXECUTION *)
let verify casp spec prog =
  match Sygus.verify casp prog spec with
  | VerifySuccess ->
    print_log "Verification succeeded!\n";
    print_out "succeeded\n"; 0
  | VerifyFailure (init_conf, final_conf) ->
    print_log
      "Verification failed!\nWith counterexample:\nINITIAL:\n%s\nFINAL:\n%s\n"
      (SC.string_of_config init_conf) (SC.string_of_config final_conf);
    print_out "failed\n"; 1

(* print program with extern label declarations *)
let export casp p =
  List.map (fun (i, _) -> "(extern "^i^")") (SM.bindings casp.lbls) @
  List.map PA.string_of_inst p
  |> String.concat "\n"

(* SYNTHESIS USING SYMBOLIC EXECUTION *)
let synth casp spec =
  let max_insts = !settings.max_insts in
  match Sygus.synth casp spec max_insts with
  | SynthSuccess p ->
    print_log "Synthesis with %s insts succeeded! Prog:\n%s\n"
      (string_of_int (List.length p)) (export casp p);
    print_out "%s\n" (export casp p); 0
  | SynthFailure ->
    print_log "Synthesis failed!\n"; 0

(* SYNTHESIS USING SYMBOLIC EXECUTION WITH SKETCHING*)
let sketch casp spec sk =
  (* print program with extern label declarations *)
  match Sygus.sketch casp spec sk with
  | SynthSuccess p ->
    print_log "Sketching synthesis with %s insts succeeded! Prog:\n%s\n"
      (string_of_int (List.length p))
      (export casp p);
    print_out "%s\n" (export casp p); 0
  | SynthFailure ->
    print_log "Sketching synthesis failed!\n"; 0

(* SYNTHESIS USING SYMBOLIC EXECUTION WITH DEDUCTION *)
let deduce casp spec =
  let res =
    match Deduce.deduce casp spec with
    | DeduceSuccess p ->
      print_log "Deductive synthesis succeeded! Prog:\n%s\n"
        (export casp p);
      print_out "%s\n" (export casp p); 0
    | DeduceFailure ->
      print_log "Deductive synthesis failed!\n"; 0
  in
  res

(* EXTRACT COMMAND *)
let extract casp prog =
  print_out "%s\n" (Extract.to_asm casp prog);
  0

let bitsize casp =
  let inst = Symexec.next_sym_inst casp in
  print_log "search space size: %f\n" (Bitsize.bitsize_of_sym_inst inst);
  0

let do_command casp cmd args =
  (* parse machine description *)
  let casp = Casp_lex.parse_with Casp_parse.casp_file casp in
  (* preprocessing passes *)
  let casp = Process.process_casp casp in
  (* execute command *)
  match (cmd, args) with
  | (Some Opt.Interp, [prog; init]) ->
    let (casp, init) = process_init casp init in
    let prog = process_prog casp prog in
    interp casp prog init
  | (Some Opt.Verify, [spec; prog]) ->
    let (casp, spec) = process_spec casp spec in
    let prog = process_prog casp prog in
    verify casp spec prog
  | (Some Opt.Synth, [spec]) ->
    let (casp, spec) = process_spec casp spec in
    synth casp spec
  | (Some Opt.Sketch, [spec; sk]) ->
    let (casp, spec) = process_spec casp spec in
    let sk = process_sketch casp sk in
    sketch casp spec sk
  | (Some Opt.Deduce, [spec]) ->
    let (casp, spec) = process_spec casp spec in
    deduce casp spec
  | (Some Opt.Extract, [prog]) ->
    let prog = Casp_lex.parse_with Casp_parse.prog_file prog in
    extract casp prog
  | (Some Opt.Bitsize, []) ->
    bitsize casp
  | (Some Opt.Interp, _) ->
    failwith ("Interp got wrong number of args "^
              (string_of_int (List.length args))^
              ": expected 2 (prog, init)")
  | (Some Opt.Verify, _) ->
    failwith ("Verify got wrong number of args "^
              (string_of_int (List.length args))^
              ": expected 2 (spec, prog)")
  | (Some Opt.Synth, _) ->
    failwith ("Synth got wrong number of args "^
              (string_of_int (List.length args))^
              ": expected 1 (spec)")
  | (Some Opt.Sketch, _) ->
    failwith ("Sketch Synth got wrong number of args "^
              (string_of_int (List.length args))^
              ": expected 2 (spec, sketch)")
  | (Some Opt.Deduce, _) ->
    failwith ("Deduce got wrong number of args "^
              (string_of_int (List.length args))^
              ": expected 2 (spec, insts)")
  | (Some Opt.Extract, _) ->
    failwith ("Extract got wrong number of args "^
              (string_of_int (List.length args))^
              ": expected 1 (prog)")
  | (Some Opt.Bitsize, _) ->
    failwith ("Bitsize got wrong number of args "^
              (string_of_int (List.length args))^
              ": expected 0")
  | (None, _) -> 0

let get_out_ch out =
  if out <> "" then open_out out
  else stdout

let casp_main () =
  (* record start time *)
  let t = Unix.gettimeofday () in

  (* gather settings *)
  Opt.parse_args ();
  settings := {
    out_ch = get_out_ch !Opt.outfile;
    log_ch = get_out_ch !Opt.logfile;
    smt_ch = get_out_ch !Opt.smtfile;

    synth_verbose = !Opt.synth_verbose;
    debugging = !Opt.debugging;
    dump_interp = !Opt.dump_interp;
    dump_solver = !Opt.dump_solver;

    dry_run = !Opt.dry_run;
    max_insts = !Opt.max_insts;
    bucket = !Opt.bucket;
    accumulation_direct = !Opt.accumulation_direct;
    accumulation_operation = !Opt.accumulation_operation;
    accumulation_category = !Opt.accumulation_category;
    sorting = !Opt.sorting;
    weak_coerce = !Opt.weak_coerce;
    no_unify = !Opt.no_unify;
    no_depend = !Opt.no_depend;
    no_branch = !Opt.no_branch;

    cex_solver = !Opt.cex_solver;
    syn_solver = !Opt.syn_solver;

    seed = !Opt.seed;
    whiten = !Opt.whiten;
  };

  (* log configuration *)
  (* TODO log more configuration *)
  print_log "Command: %s\n" (Opt.string_of_command_args ());
  print_log "Output to: %s\n" !Opt.outfile;
  print_log "Log to: %s\n" !Opt.logfile;
  if !settings.seed <> 0 then begin
    Random.init !settings.seed;
    print_log "Set random seed: %s\n" (string_of_int !settings.seed);
  end;

  (* execute *)
  try
    let res =
      match !Opt.files with
      | casp :: args -> do_command casp !Opt.cmd args
      | [] -> failwith "No files given: need a casp file"
    in
    print_log "\tExecution Time: %fs\n" (Unix.gettimeofday () -. t);
    res
  with e ->
    print_log "Fatal error: exception %s\n" (Printexc.to_string e);
    raise e

let _ = casp_main () |> exit
