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


module P = Smttree
module A = Ast

let conv'ty ty =
   match ty with
   | P.BOOL _pos -> A.BOOL
   | P.INT _pos -> A.INT
   | P.BV (_pos, _w) -> A.BV

let rec conv'expr e =
   match e with
   | P.CONST (pos, k, ty) -> A.CONST (pos, k, conv'ty ty)
   | P.READVAR (pos, x) -> A.READVAR (pos, x, A.BOOL)
   | P.OP (pos, op, args) ->
        let args' = List.map conv'expr args in
        match op with
        | P.LOGNOT -> A.BOOLOP (pos, A.LOGNOT, args')
        | P.LOGAND -> A.BOOLOP (pos, A.LOGAND, args')
        | P.LOGOR -> A.BOOLOP (pos, A.LOGOR, args')
        | P.EQ -> A.INTOP (pos, A.INTEQ, args')
        | P.LT -> A.INTOP (pos, A.INTLT, args')
        | P.ADD -> A.INTOP (pos, A.INTADD, args')
        | P.SUB -> A.INTOP (pos, A.INTSUB, args')
        | P.BITOR -> A.BVOP (pos, A.BVBITOR, args')
        | P.BITADD -> A.BVOP (pos, A.BVADD, args')
        | P.BITSUB -> A.BVOP (pos, A.BVSUB, args')
        | P.BITUSHR -> A.BVOP (pos, A.BVUSHR, args')
        | P.BITSHL -> A.BVOP (pos, A.BVSHL, args')
        | P.ZEROEXTEND _w -> begin
             (*A.BVOP (pos, A.ZEROEXTEND w, args')*)
             match args' with
             | [arg'] -> arg'
             | _ -> Pos.crashat pos ("Wrong number of args for zeroextend")
          end
        | P.BV2INT -> begin
             match args' with
             | [arg'] -> A.BV2INT (pos, arg')
             | _ -> Pos.crashat pos ("Wrong number of args for bv2int")
          end
        | P.ITE -> begin
             match args' with
             | [c; t; f] -> A.IF (pos, c, t, f)
             | _ -> Pos.crashat pos ("Wrong number of args for ite")
          end

let conv'stmt s =
   match s with
   | P.DECLARE_FUN (pos, name, ty) ->
        A.DECL (pos, name, conv'ty ty)
   | P.DEFINE_FUN (pos, name, ty, e) ->
        A.LET (pos, name, conv'ty ty, conv'expr e)
   | P.ASSERT (pos, e) ->
        A.ASSERT (pos, conv'expr e)
   | P.PUSH pos -> A.MISC (pos, "push")
   | P.POP pos -> A.MISC (pos, "pop")
   | P.CHECK_SAT pos -> A.MISC (pos, "check-sat")
   | P.GET_MODEL pos -> A.MISC (pos, "get-model")
   | P.SET_OPTION (pos, name, tf) ->
       let s = if tf then "true" else "false" in
       A.MISC (pos, "set-option " ^ name ^ " " ^ s)
   | P.EXIT pos -> A.MISC (pos, "exit")

let go stmts =
   List.map conv'stmt stmts
