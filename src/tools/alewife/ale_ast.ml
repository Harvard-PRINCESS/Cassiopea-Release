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


open Batteries
open Util

open BatTuple.Tuple5
open BatTuple.Tuple2

module BI = BatBig_int
module R  = BatText

let (++) = (^)

type id  = string

type subst = id * id

type width =
  | ConcWidth of Util.bint
  | SymWidth of string

type typ =
  | BoolType
  | IntType
  | LblType of width
  | BitType
  | VecType of width
  | PtrType of width
  | RegType of width
  | AbsType of  id     (* interpreted only by the machine model *)
  | FunType of  typ list * typ

type unop =
  | Neg
  | LogNot
  | BitNot

type binop =
  | Add
  | Sub
  | Mul
  | Div
  | Eq
  | Neq
  | Lt
  | Gt
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

type expr = 
  | Atomic of atomic
  | Deref of expr
  (* | Label of id *)
  | Fetch of expr
  | Index of expr * expr
  | Slice of expr * expr * expr
  | Implies of expr * expr
  | Unop of unop * expr
  | Binop of expr * binop * expr
  | App of id * expr list
  | LetE of id * typ * expr * expr
  | IfE of expr * expr * expr

type param = id * typ

type require = 
  | RequireType of id
  | RequireVal of id * typ
  | RequireFunc of id * typ

type provide = 
  | ProvideType of id * typ
  | ProvideVal of id * typ * expr
  | ProvideFunc of id * param list * typ * expr
  
type frame = 
  | FrameLabel of id * width * width * width * id
  | FrameRegion of id * width * width * width (* machine memory declaration *)
  | FrameModifyReg of id list
  | FrameModifyMem of (id * width) list
  | FrameInvariant of expr

type block_let = id * typ * expr
type block_spec = frame list * block_let list * expr * expr
type block = id * block_spec
type t = require list * provide list * block option

(* pretty print *)
let string_of_width = function
  | SymWidth x -> x
  | ConcWidth c -> BI.string_of_big_int c

let rec string_of_typ = function
  | BoolType -> "bool"
  | IntType -> "int"
  | LblType w -> string_of_width w ^ " label"
  | BitType -> "bit"
  | VecType w -> string_of_width w ^ " vec"
  | PtrType w -> string_of_width w ^ " ptr"
  | RegType w -> string_of_width w ^ " reg"
  | AbsType id -> id
  | FunType (args, ret) ->
       let args' = List.map string_of_typ args in
       "("^(String.concat ", " args')^") -> "^(string_of_typ ret)

let string_of_id i = i
let string_of_ids ii = List.fold_left (fun s i -> i ++ " " ++ s) "" ii

let string_of_consptr (i, o) =
  "["^(string_of_id i)^", "^(string_of_int o)^"]"
let string_of_ptr (i, o) =
  "["^(string_of_id i)^", "^(string_of_width o)^"]"
let string_of_ptrs pp = List.fold_left (fun s i -> ((string_of_ptr i) ++ " " ++ s)) "" pp

let string_of_atomic = function
  | Id i -> string_of_id i
  | Int i -> string_of_bint i
  | Bool b -> if b then "true" else "false"
  | Vec v -> Bits.to_bitstring v
  | Ptr (i, o) -> "["^(string_of_id i)^", "^(string_of_bint o)^"]"

let name_of_unop = function
  | Neg -> "(-)"
  | LogNot -> "!"
  | BitNot -> "~"

let name_of_binop = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Eq -> "=="
  | Neq -> "!="
  | Lt -> ">"
  | Gt -> "<"
  | LShift -> "<<"
  | RShift -> ">>"
  | LogAnd -> "&&"
  | LogOr -> "||"
  | LogXor -> "^^"
  | BitAnd -> "&"
  | BitOr -> "|"
  | BitXor -> "^"

let rec string_of_expr = function
  | Atomic a -> string_of_atomic a
  | Deref e -> "*"^(string_of_expr e)
  (* | Label i -> "{"^(string_of_id i)^"}" *)
  | Fetch e -> "read["^(string_of_expr e)^"]"
  | Index (e1, e2) -> (string_of_expr e1)^"["^(string_of_expr e2)^"]"
  | Slice (e1, e2, e3) -> (string_of_expr e1)^"["^(string_of_expr e2)^": "^(string_of_expr e3)^"]"
  | LetE (i, ty, e1, e2) -> "let "^(string_of_id i)^" : "^(string_of_typ ty)^" = "^(string_of_expr e1) ^" in "^(string_of_expr e2)
  | IfE (e1, e2, e3) -> "if "^(string_of_expr e1)^" then "^(string_of_expr e2)^" else "^(string_of_expr e3)
  | App (i, args) -> i :: (args |> List.map string_of_expr) |> String.concat " "
  | Implies (e1, e2) -> (string_of_expr e1)^" -> "^(string_of_expr e2)
  | Unop (u, e) -> (name_of_unop u)^" "^(string_of_expr e)
  | Binop (e1, b, e2) -> (string_of_expr e1)^" "^(name_of_binop b)^" "^(string_of_expr e2)

let string_of_require = function
  | RequireType i -> "require_type "^(string_of_id i)
  | RequireVal (i, t)  -> "require_val "^(string_of_id i)^" "^(string_of_typ t)
  | RequireFunc (i, t) -> "require_fun "^(string_of_id i)^" "^(string_of_typ t)

let string_of_provide = function
  | ProvideType (i, t) -> "provide_type "^(string_of_id i)^" = "^(string_of_typ t)
  | ProvideVal (i, t, e) -> "provide_val "^(string_of_id i)^" : "^(string_of_typ t)^" = "^(string_of_expr e)
  | ProvideFunc (i, ps, t, e) -> 
    let args = List.map (fun (x, y) -> (string_of_id x)^" : "^(string_of_typ y)) ps in
    "provide_fun "^(string_of_id i)^" ("^(String.concat " " args)^") : "^(string_of_typ t)^" = "^(string_of_expr e)

let string_of_frame = function
  | FrameLabel (i1, b, l, r, i2) -> "region "^(string_of_id i1)^" : "^(string_of_width b)^" bit "^(string_of_width l)^" len "^(string_of_width r)^" ref with label "^(string_of_id i2)
  | FrameRegion (name, b, l, r) -> "region "^(string_of_id name)^" : "^(string_of_width b)^" bit "^(string_of_width l)^" len "^(string_of_width r)^" ref"
  | FrameModifyReg ii -> "register modifies: "^(string_of_ids ii)
  | FrameModifyMem pp -> "memory modifies: "^(string_of_ptrs pp)
  | FrameInvariant e -> "invariant: "^(string_of_expr e)

let string_of_blocklet (i, t, e) = 
  "let "^(string_of_id i)^" : "^(string_of_typ t)^" = "^(string_of_expr e)

let string_of_blockspec (fs, ls, pre, post) =
  let frames = List.map string_of_frame fs in
  let blocklets = List.map string_of_blocklet ls in
  (String.concat "\n" blocklets)^"\n"^
  "frame:\n"^(String.concat "\n" frames)^"\n"^
  "pre:\n"^(string_of_expr pre)^"\n"^
  "post: \n"^(string_of_expr post)^"\n"

let string_of_block (_i, bs) = string_of_blockspec bs

let string_of_ast (rs, ps, bls) =
   let strings =
      List.map string_of_require rs @
      List.map string_of_provide ps @
      List.map string_of_block bls
   in
   String.concat "\n" strings

let to_string (i, bs) = string_of_block (i, bs)
