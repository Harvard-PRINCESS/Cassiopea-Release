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

(* verification calls for cassiopeia *)

(* reporting results of verification *)
(* VerifySuccess: nothing is wrong *)
(* VerifyFailure: carries counterexample initial/final states *)
type verify_result =
  | VerifySuccess
  | VerifyFailure of config * config

(*************************************************************************)
let verify casp prog spec =
  let spec = eval_spec casp spec in
  let sp = lift_prog casp prog in

  if !settings.debugging then begin
    print_log "SPECIFICATION:\n%s\n" (string_of_sspec spec);
    flush_log ()
  end;

  (* create initial state *)
  let init = config_of_pred spec.casp spec.pre in

  (* execute symbolic program; get final state *)
  let final =
    match exec_prog sp init with
    | Ok final -> final
    | Error (pos, s) ->
      failwith ("program evaluation failed at "^(Pos.string_of pos)^"\n"^
                "with error: "^s)
  in

  let term = apply_spec spec sp init final in

  let cond = log_and
    (log_and term.assumes term.axioms)
    (log_not term.asserts)
  in

  (* solve for an initial state that leads to a violated postcond *)
  match esolve cond with
  (* no counterexamples found *)
  | None -> VerifySuccess
  (* found a counterexample *)
  | Some cex ->
    let init = subst_config cex init in
    let final = subst_config cex final in

    VerifyFailure (init, final)
