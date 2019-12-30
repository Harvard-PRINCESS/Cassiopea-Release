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

module P = Casptree
module A = Ast

let rec conv'expr e =
   match e with
   | P.BITCONST (pos, k, _w) -> A.CONST (pos, k, BV)
   | P.INTCONST (pos, k) -> A.CONST (pos, k, INT)
   | P.READVAR (pos, x) -> A.READVAR (pos, x, A.BOOL)
   | P.OP (pos, op, args) ->
        let args' = List.map conv'expr args in
        match op with
        | P.LOGNOT -> A.BOOLOP (pos, A.LOGNOT, args')
        | P.LOGAND -> A.BOOLOP (pos, A.LOGAND, args')
        | P.LOGOR -> A.BOOLOP (pos, A.LOGOR, args')
        | P.EQ -> A.INTOP (pos, A.INTEQ, args')
        | P.INTLT -> A.INTOP (pos, A.INTLT, args')
        | P.ADD -> A.INTOP (pos, A.INTADD, args')
        | P.SUB -> A.INTOP (pos, A.INTSUB, args')
        | P.BITAND -> A.BVOP (pos, A.BVBITAND, args')
        | P.BITOR -> A.BVOP (pos, A.BVBITOR, args')
        | P.BITADD -> A.BVOP (pos, A.BVADD, args')
        | P.BITSUB -> A.BVOP (pos, A.BVSUB, args')
        | P.BITUSHR -> A.BVOP (pos, A.BVUSHR, args')
        | P.BITSHL -> A.BVOP (pos, A.BVSHL, args')
        | P.BITLT -> A.BVOP (pos, A.BVLT, args')
        | P.SLICE (a, b) -> begin
             match args' with
             | [arg'] -> A.SLICE (pos, arg', a, b)
             | _ -> Pos.crashat pos ("Wrong number of args for slice")
          end
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

let gettype x =
   if String.sub x 0 4 = "bool" then A.BOOL
   else if String.sub x 0 3 = "bv_" then A.BV
   else if String.sub x 0 3 = "int" then A.INT
   else Util.crash ("caspconv: unexpected variable name " ^ x)

let getdecls e0 =
   let env = ref Types.StringMap.empty in
   let rec getvars e =
      match e with
      | P.BITCONST _ -> ()
      | P.INTCONST _ -> ()
      | P.READVAR (pos, x) -> begin
           try
              let _ = Types.StringMap.find x !env in ()
           with Not_found ->
              let d = A.DECL (pos, x, gettype x) in
              env := Types.StringMap.add x d !env
        end
      | P.OP (_, _, args) ->
           List.iter getvars args
   in
   getvars e0;
   List.map (fun (_x, d) -> d) (Types.StringMap.bindings !env)

let go e =
   let ds = getdecls e in
   let e' = conv'expr e in
   ds @ [A.ASSERT (Pos.builtin, e')]

