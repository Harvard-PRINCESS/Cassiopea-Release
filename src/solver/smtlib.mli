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
open Symvars

(* maintain a mapping from names to smtlib expressions *)
(* also maintains:
   - relationship between cassiopeia-level named symbolic values and internal names,
     to allow interpretation of the solution that comes back from the solver
   - which subexprs have already been encoded, allowing efficient reuse *)
type env
val env_empty : env

(* first, a mechanism for managing the representation of symbolic values
   as variables in the solver *)
(* takes:
   - symbolic value
   - environment *)
(* produces: a new name and a new environment, in which the name is mapped to
   the encoded symbolic value *)
(* environment may have had many mappings added, corresponding to
   subexpressions: this is useful for optimizing overlapping expressions *)
(* each mapping is converted directly to a line of smtlib2: viz. *)
(* (define-fun e35 () (_ BitVec 8) (ite e33 c34 e9)) *)
val encode : 'a sym_value -> env -> (id * env)
(* here, lots of recursion over symbolic values... *)

(* second, helpers for smtlib code gen *)
val declare_fun : id -> string -> string -> string (* as in name, domain, range *)
val define_fun : id -> string -> string -> string -> string (* as in name, args, type, definition *)
val declare_const : id -> string -> string (* as in name, type *)
val define_const : id -> string -> string -> string (* as in name, type, definition *)

(* this is the final encoding function, turning an env into a giant chunk of
   smtlib definitions that can go to the solver *)
val string_of_env : env -> string

(* encode new values in an environment, omitting already-encoded declarations *)
(* takes: new environment, old environment *)
(* TODO this is a bad hack *)
val string_of_env_new : env -> env -> string

(* decode interprets the smtlib response text *)
(* takes:
   - smtlib response text
   - env carrying information about what variables represent what symbolic values *)
(* produces: solution object *)
val decode : Smtlib_ast.t -> env -> model
