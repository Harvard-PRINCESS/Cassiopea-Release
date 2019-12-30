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

(* cassiopeia machine description *)
type casp_file = {
  wordsize : int;
  types : typ SM.t;                     (* type aliases *)
  lets : (atomic * typ) SM.t;           (* pure let bindings *)
  txts : string SM.t;                   (* string txt bindings *)
  regs : int SM.t;                      (* register definitions *)
  mems : (int * int * int * id option) SM.t;  (* memory definitions *)
  lbls : string SM.t;                   (* label -> memory region mapping *)
  invs : expr list;                     (* invariant expression list *)
  defs : (arg list * typ * expr) SM.t;  (* pure function defs *)
  defss : (arg list * stmt) SM.t;       (* subroutine defs *)
  defops : (arg list * stmt) SM.t;      (* operation defs *)
  defstr : (arg list * expr) SM.t;      (* operation asm generation defs *)
  opcategory : (SS.t SM.t) SM.t;        (* operation ID set categorized by type *)
}

let casp_file_empty = {
  wordsize = 199; (* default word size = 199 bit *)
  types = SM.empty;
  lets = SM.empty;
  txts = SM.empty;
  regs = SM.empty;
  mems = SM.empty;
  lbls = SM.empty;
  invs = [];
  defs = SM.empty;
  defss = SM.empty;
  defops = SM.empty;
  defstr = SM.empty;
  opcategory = SM.empty;
}

(* cassiopeia specification *)
type spec_file = {
  modifyreg : SS.t;                (* modify reg list *)
  modifymem : (id * int) list;        (* modify pointer list *)
  lets : (string * typ * expr) list;  (* let bindings in order *)
  precond : expr;
  postcond : expr;
}
