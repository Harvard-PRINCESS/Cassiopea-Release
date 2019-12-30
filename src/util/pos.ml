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


(* Module for positions in source *)
open Batteries

open BatTuple.Tuple5

module P = Printf

type t = (string * int * int * int * int) option

type pos = t

let file_of p =
  match p with
  | Some p -> first p
  | None -> "<none>"
let line_beg p =
  match p with
  | Some p -> second p
  | None -> 0
let line_end p =
  match p with
  | Some p -> third p
  | None -> 0
let col_beg p =
  match p with
  | Some p -> fourth p
  | None -> 0
let col_end p =
  match p with
  | Some p -> fifth p
  | None -> 0

let mk f lb le cb ce = Some (make f lb le cb ce)
let none = mk "<none>" 0 0 0 0
let builtin = none

let string_of pos =
  match pos with
  | Some _ ->
    P.sprintf "%s:%d,%d-%d,%d"
      (file_of pos)
      (line_beg pos)
      (col_beg  pos)
      (line_end pos)
      (col_end  pos)
  | None -> "<none>"

let print p =
  string_of p |>
  P.printf "%s"

let lines_of p =
  let b, e = line_beg p, line_end p in
  let _ = assert (e - b >= 0) in
  (b, e - b)

let cols_of p =
  let b, e = col_beg p, col_end p in
  let _ = assert (e - b >= 0) in
  (b, e - b)

(* based on grouper's pos.ml, 20190904 *)
let divide pos k =
  match pos with
  | Some (file, startline, startcolumn, endline, endcolumn) ->
    let newcolumn = startcolumn + k in
    let p1 = Some (file, startline, startcolumn, endline, newcolumn) in
    let p2 = Some (file, startline, newcolumn, endline, endcolumn) in
    (p1, p2)
  | None -> (None, None)
