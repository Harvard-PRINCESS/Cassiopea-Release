(*
 * Copyright (c) 2019
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

(*
 * Even though we're going to spit this out again in C syntax, and
 * we're only doing minimal processing, it's still better to transform
 * the declarations to a sane layout and back again.
 *
 * However, we don't need to keep anything we don't need to figure
 * out what we're doing...
 *)

type typename =
     VOID
   | CHAR | SCHAR | UCHAR
   | SHORT | USHORT
   | INT | UINT
   | LONG | ULONG
   | LONGLONG | ULONGLONG
   | FLOAT | DOUBLE | LDOUBLE
   | STRUCT of string
   | UNION of string
   | ENUM of string
   | USETYPEDEF of string
   | POINTER of typename
   | CONST of typename
   | RESTRICT of typename
   | VOLATILE of typename
   | ARRAYTYPE of (typename (* *int *) )
   | BITFIELD of (typename (* *int *) )
   | FUNCTYPE of (typename * param list)
   | KRFUNCTYPE of (typename * string list)

and param =   (* isregister, type *)
     PARAM of (bool * typename)
   | MOREPARAMS

type typedecl =
     STRUCTDECL of (Pos.pos * unit) (* don't need the body *)
   | UNIONDECL of (Pos.pos * unit) (* don't need the body *)
   | ENUMDECL of (Pos.pos * unit) (* don't need the body *)

type spec = {
   tagdecls: (Pos.pos * typedecl) Types.StringMap.t;
   typedefs: (Pos.pos * typename) Types.StringMap.t;
   funcdecls: (Pos.pos * typename) Types.StringMap.t;
   gencalls: (Pos.pos * string) list;
}
