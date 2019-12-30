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

type boolop =
| LOGNOT
| LOGAND
| LOGOR
| LOGEQ

type intop =
| INTEQ
| INTLT
| INTADD
| INTSUB

type bvop =
| BVEQ
| BVLT
| BVADD
| BVSUB
| BVBITAND
| BVBITOR
| BVUSHR
| BVSHL

type typename =
| BOOL
| INT
| BV

type expr =
| CONST of Pos.pos * int * typename
| READVAR of Pos.pos * string * typename
| IF of Pos.pos * expr * expr * expr
| SLICE of Pos.pos * expr * int * int
| BV2INT of Pos.pos * expr
| BOOLOP of Pos.pos * boolop * expr list
| INTOP of Pos.pos * intop * expr list
| BVOP of Pos.pos * bvop * expr list

type stmt =
| ASSERT of Pos.pos * expr
| DECL of Pos.pos * string * typename
| LET of Pos.pos * string * typename * expr
| MISC of Pos.pos * string
