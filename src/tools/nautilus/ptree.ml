(*
 * Copyright (c) 2018
 *	The President and Fellows of Harvard College.
 *
 * Written by David A. Holland.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE UNIVERSITY AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE UNIVERSITY OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *)

type uop =
     POSTINC | POSTDEC | PREINC | PREDEC
   | ADDROF | INDIR
   | NEG
   | BITNOT | LOGNOT

type bop =
     SEQ
   | ASSIGN
   | BITXORASSIGN | BITORASSIGN | BITANDASSIGN | LSHIFTASSIGN | RSHIFTASSIGN
   | ADDASSIGN | SUBASSIGN | MULASSIGN | DIVASSIGN | MODASSIGN
   | LOGOR | LOGAND
   | BITOR | BITXOR | BITAND
   | EQ | NEQ
   | LT | GT | LTEQ | GTEQ
   | LSHIFT | RSHIFT
   | ADD | SUB | MUL | DIV | MOD
   | READARRAY

type storageclass =
   AUTO | REGISTER | STATIC | EXTERN | TYPEDEF

type typequal =
   CONST | VOLATILE | RESTRICT

type expr =
     INTCONSTANT of (Pos.pos * string)
   | FLOATCONSTANT of (Pos.pos * string)
   | CHARCONSTANT of (Pos.pos * string)
   | STRCONSTANT of (Pos.pos * string)
   | READVAR of (Pos.pos * string)
   | READFIELD of (Pos.pos * expr * string)
   | READPTRFIELD of (Pos.pos * expr * string)
   | UOP of (Pos.pos * uop * expr)
   | BOP of (Pos.pos * expr * bop * expr)
   | CALL of (Pos.pos * expr * expr list)
   | ESIZEOF of (Pos.pos * expr)
   | SIZEOF of (Pos.pos * cdecl)
   | CAST of (Pos.pos * cdecl * expr)
   | IFEXPR of (Pos.pos * expr * expr * expr)

and enumerator =
   ENUMERATOR of (Pos.pos * string * expr option)

and typespec =
     VOID | CHAR | SHORT | INT | LONG | FLOAT | DOUBLE | SIGNED | UNSIGNED
   | STRUCT of (Pos.pos * string option * cdecl list option)
   | UNION of (Pos.pos * string option * cdecl list option)
   | ENUM of (Pos.pos * string option * enumerator list option)
   | USETYPEDEF of string

and declspec =
     STORAGECLASS of storageclass
   | TYPESPEC of typespec
   | TYPEQUAL of typequal

and pointer =
   POINTER of (Pos.pos * typequal list * pointer option)

and initializer_ =
     INITEXPR of (Pos.pos * expr)
   | INITLIST of (Pos.pos * initializer_ list)

and declarator =
     DECLABS of Pos.pos
   | DECLNAME of (Pos.pos * string)
   | DECLARRAY of (Pos.pos * declarator * expr option)
   | DECLFUNC of (Pos.pos * declarator * cdecl list)
   | KRDECLFUNC of (Pos.pos * declarator * string list)
   | DECLPOINTER of (Pos.pos * pointer * declarator)
   | DECLBITFIELD of (Pos.pos * declarator option * expr)
   | DECLINIT of (declarator * initializer_)

and cdecl =
     DECL of (Pos.pos * declspec list * declarator)
   | DECLS of (Pos.pos * declspec list * declarator list)
   | MOREPARAMS

type decl =
     GENCALL of (Pos.pos * string)
   | CDECL of cdecl
