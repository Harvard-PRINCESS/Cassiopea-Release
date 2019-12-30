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


(* value-domain independent utilities *)

(* "fallible monad": for ops that can fail *)
(* t_ctx -> ('a, string) result * t_ctx *)

let ok a ctx = Ok (a, ctx)
let error s _ = Error s

let bind m k ctx =
  match m ctx with
  | Error e -> Error e
  | Ok (v, ctx) -> k v ctx

let bind2 m1 m2 k ctx =
  match m1 ctx with
  | Error e -> Error e
  | Ok (v1, ctx) ->
    match m2 ctx with
    | Error e -> Error e
    | Ok (v2, ctx) -> k (v1, v2) ctx

let bind3 m1 m2 m3 k ctx =
  match m1 ctx with
  | Error e -> Error e
  | Ok (v1, ctx) ->
    match m2 ctx with
    | Error e -> Error e
    | Ok (v2, ctx) ->
      match m3 ctx with
      | Error e -> Error e
      | Ok (v3, ctx) -> k (v1, v2, v3) ctx
