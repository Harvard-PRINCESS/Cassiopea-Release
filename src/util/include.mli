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

(* Add a directory to the include path. *)
val addincludepath: string -> unit

(* Include a file. First arg says whether to search the include path. *)
val includefile: bool -> string -> unit

(*
 * Wrapper between lexer and parser. Args are:
 *   - the EOF token (normally EOF)
 *   - a function for testing a token for being EOF
 *   - the real lexer
 *   - the lexbuf passed in from the parser (this is mostly ignored,
 *     but has position information loaded into it for the parser's
 *     benefit)
 *
 * Typical usage:
 *     let parser = Parser.start (includewrap EOF (fun t -> t = EOF) lexer) in
 *     parser dummylexbuf
 * where dummylexbuf is a lexbuf initialized to contain nothing interesting.
 *)
val includewrap: 'token -> ('token -> bool) ->
       (Lexing.lexbuf -> 'token) -> Lexing.lexbuf -> 'token
