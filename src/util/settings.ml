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

(* global printout setting information *)
type settings = {
  out_ch : out_channel;
  log_ch : out_channel;
  smt_ch : out_channel;

  synth_verbose : bool;
  debugging : bool;
  dump_interp : bool;
  dump_solver : bool;

  dry_run : bool;
  max_insts : int;
  bucket : bool;
  accumulation_direct : bool;
  accumulation_operation : bool;
  accumulation_category : bool;
  sorting : bool;
  weak_coerce : bool;
  no_unify : bool;
  no_depend : bool;
  no_branch : bool;

  cex_solver : string;
  syn_solver : string;

  seed : int;
  whiten : string list;
}

let settings = ref {
  out_ch = stdout;
  log_ch = stdout;
  smt_ch = stderr;

  synth_verbose = false;
  debugging = false;
  dump_interp = false;
  dump_solver = false;

  dry_run = false;
  max_insts = 4;
  bucket = false;
  accumulation_direct = false;
  accumulation_operation = false;
  accumulation_category = false;
  sorting = false;
  weak_coerce = false;
  no_unify = false;
  no_depend = false;
  no_branch = false;

  cex_solver = "z3";
  syn_solver = "btor";

  seed = 0;
  whiten = [];
}
