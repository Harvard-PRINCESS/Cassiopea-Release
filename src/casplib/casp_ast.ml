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

type typ =
  (* basic types *)
  | BitType of int
  | LocType of int
  | BoolType
  | IntType
  | StringType
  | LabelType of int
  | MemType of int * int * int (* word size, length, pointer size *)
  (* parser placeholders *)
  | AliasType of id
  | AliasLocType of id

type unop =
  | Neg
  | LogNot
  | BitNot

type binop =
  | Add
  | Sub
  | Mul
  | Div
  | Pow
  | Eq
  | Neq
  | Lt
  | Gt
  | BAdd
  | BSub
  | BMul
  | BLt
  | BGt
  | BSLt
  | BSGt
  | LShift
  | RShift
  | LogAnd
  | LogOr
  | LogXor
  | BitAnd
  | BitOr
  | BitXor

type atomic =
  | Id of id
  | Int of bint
  | Bool of bool
  | Vec of bits
  | Ptr of id * bint
  | Str of string

type op_type =
  | Typed of string * string
  | NoTyped

type arg = id * typ

type expr' =
  | Atomic of atomic
  | Deref of expr
  | Fetch of expr * expr
  | Index of expr * expr
  | Slice of expr * expr * expr
  | Unop of unop * expr
  | Binop of expr * binop * expr
  | App of id * expr list
  | LetE of id * typ * expr * expr
  | IfE of expr * expr * expr
and expr = Pos.t * expr'

type stmt' =
  | Skip
  | Err
  | Assert of expr * string
  | Seq of stmt * stmt
  | Assign of expr * expr
  | Store of expr * expr * expr
  | For of id * expr * expr * stmt
  | Call of id * expr list
  | LetS of id * typ * expr * stmt
  | IfS of expr * stmt * stmt
and stmt = Pos.t * stmt'

type decl' =
  | DeclType of id * typ
  | DeclLet of id * typ * expr
  | DeclString of id * string
  | DeclLetstate of id * typ * id option
  | DeclInvariant of expr
  | DeclDef of id * arg list * typ * expr
  | DeclDefs of id * arg list * stmt
  | DeclDefop of id * arg list * expr * op_type * stmt
and decl = Pos.t * decl'

type extern = Pos.t * id
type casp_inst = Pos.t * (id * (Pos.t * atomic) list)

type sketch_arg' =
  | SketchArg of atomic
  | SketchArgPlaceHolder
and sketch_arg = Pos.t * sketch_arg'

type sketch_inst' =
  | SketchInst of id * sketch_arg list
  | SketchInstPlaceHolder
and sketch_inst = Pos.t * sketch_inst'

type startstate' =
  | StartAssign of atomic * atomic
  | StartMem of id * int * int * int * id option
and startstate = Pos.t * startstate'

type submodule = Pos.t * id * decl list * id list * (id * int) list

type frame' =
  | FrameModifyReg of id list
  | FrameModifyMem of (id * int) list
and frame = Pos.t * frame'

type spec = decl list * frame list * expr * expr

(* name_of functions provide descriptive appellations for error messages. *)

let name_of_typ = function
  | BitType _ -> "bitvector"
  | LocType _ -> "location"
  | BoolType -> "boolean"
  | IntType -> "integer"
  | MemType (_, _, _) -> "memory"
  | _ -> failwith "alias type in type check pass?"

let name_of_unop = function
  | Neg -> "Negation"
  | LogNot -> "Logical Not"
  | BitNot -> "Bitwise Not"

let name_of_binop = function
  | Add -> "Add"
  | Sub -> "Sub"
  | Mul -> "Mul"
  | Div -> "Div"
  | Pow -> "Pow"
  | Eq -> "Eq"
  | Neq -> "Neq"
  | Lt -> "Lt"
  | Gt -> "Gt"
  | BAdd -> "Bitvector Add"
  | BSub -> "Bitvector Sub"
  | BMul -> "Bitvector Mul"
  | BLt -> "Bitvector Lt"
  | BGt -> "Bitvector Gt"
  | BSLt -> "Bitvector Signed Lt"
  | BSGt -> "Bitvector Signed Gt"
  | LShift -> "LShift"
  | RShift -> "RShift"
  | LogAnd -> "Logical And"
  | LogOr -> "Logical Or"
  | LogXor -> "Logical Xor"
  | BitAnd -> "Bitwise And"
  | BitOr -> "Bitwise Or"
  | BitXor -> "Bitwise Xor"
