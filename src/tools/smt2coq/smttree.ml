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


type op =
| LOGNOT
| LOGAND
| LOGOR
| EQ
| LT
| ADD
| SUB
| BITOR
| BITADD
| BITSUB
| BITUSHR
| BITSHL
| ZEROEXTEND of int
| BV2INT
| ITE

type typename =
| BOOL of Pos.pos
| INT of Pos.pos
| BV of Pos.pos * int

type expr =
| CONST of Pos.pos * int * typename
| READVAR of Pos.pos * string
| OP of Pos.pos * op * expr list

type stmt =
| DECLARE_FUN of Pos.pos * string * typename
| DEFINE_FUN of Pos.pos * string * typename * expr
| ASSERT of Pos.pos * expr
| PUSH of Pos.pos
| POP of Pos.pos
| CHECK_SAT of Pos.pos
| GET_MODEL of Pos.pos
| SET_OPTION of Pos.pos * string * bool
| EXIT of Pos.pos

