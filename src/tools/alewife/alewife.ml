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

module ALex = Ale_lex
module CLex = Casp_lex
module AAst = Ale_ast
module CAst = Casp_ast

module A   = Arg
module S   = Sys
module P   = BatPrintf

let (++) = (^)

let files: string list ref    = ref []
let outfile:      string ref  = ref ""

let usage =
  "Usage: " ++ exe ++ " alewife_file casp_machine_description mapping_file [-o output_file]"

let opts = [
  ("-o", A.Set_string outfile, ": set file for outputs")]

let parse_args () =
  A.parse opts (arl files) usage

let ale_main () =
  parse_args ();
  match !files with
  | [] -> failwith "No files given: need an alewife file"
  | afile :: cfile :: mfile :: [] -> 
    (* parse alewife spec file *)
    P.printf "Parsing %s...\t" afile;
    let ale = ALex.read afile in
    let ale = match ale with
      | ([], [], None) -> afile ++ " is empty\n" |> failwith
      | _ -> ale in (* requires; provides; blocks *)
    P.printf "Parsed.\n";    
    (* P.printf "Saw program: \n\n%s.\n" (AAst.string_of_ast ale); *)
    (* parse casp mapping file *)
    let casp = Casp_lex.parse_with Casp_parse.casp_file cfile in
    let map = Casp_lex.parse_with Casp_parse.map_file mfile in
    let ale = Specnew.process_all ale casp map in 
    (* let ale = Spec.process_ale ale casp map in *)
    let out_ch = if !outfile <> "" then open_out !outfile else stdout in
    P.fprintf out_ch "%s\n" ale;
    P.printf "\tMachine-Dependent Spec Printed.\n";    
    0
  | _ -> failwith "Error! Usage: <alewife> alewife_file casp_machine_description mapping_file [-o output_file]"

let _ = ale_main ()
