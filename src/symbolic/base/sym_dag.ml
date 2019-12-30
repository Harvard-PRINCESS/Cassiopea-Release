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
open Hashcons

open Sym_ast
open Sym_hash
open Sym_map

(* symbolic expressions as DAGs; utilities for traversal and manipulation *)

type dag = {
  (* list of nodes in toposort order *)
  nodes : sym_ex_t list;
  (* sets of (predecessors, successors) for each node *)
  edges : (SVS.t * SVS.t) SVM.t;
  (* set of nodes to be considered root nodes *)
  roots : SVS.t;
}

(* get successors of a value as existentials *)
let get_successors : type a. a sym_value -> sym_ex_t list =
  fun v ->
  match v.node with
  | SymVal (IsInt, _) -> []
  | SymVal (IsBool, _) -> []
  | SymVal (IsLoc _, _) -> []
  | SymVal (IsVec _, _) -> []
  | SymVal (IsPtr _, (_, o)) ->
    [ex_of_sym_value o]
  | SymVal (IsWord _, BitVec w) ->
    [ex_of_sym_value w]
  | SymVal (IsWord _, BitPtr w) ->
    [ex_of_sym_value w]
  | SymInt _ -> []
  | SymBool _ -> []
  | SymVec (_, _) -> []
  | SymUnop (_, v') ->
    [ex_of_sym_value v']
  | SymBinop (_, v1, v2) ->
    [ex_of_sym_value v1; ex_of_sym_value v2]
  | SymIte (b, v1, v2) ->
    [ex_of_sym_value b; ex_of_sym_value v1; ex_of_sym_value v2]
  | SymMultiop (_, ls, _, _) ->
    List.map ex_of_sym_value ls
  | SymChoose (ls, tl) ->
    let ex_of_pair ls (b, v) =
      ex_of_sym_value b :: ex_of_sym_value v :: ls
    in
    List.fold_left ex_of_pair [ex_of_sym_value tl] ls

let get_successors' x =
  match x.node with
  | Ex (_, v) -> get_successors v

(* empty DAG *)
let dag_empty =
  { nodes = [];
    edges = SVM.empty;
    roots = SVS.empty; }

(* check whether node is present in DAG *)
let dag_mem' x dag =
  match SVM.find_opt x dag.edges with
  | None -> false
  | Some _ -> true

let dag_mem v dag = dag_mem' (ex_of_sym_value v) dag

(* add node and its successors to DAG *)
let rec dag_add' x dag =
  if dag_mem' x dag then
    dag
  else
    let successors = get_successors' x in
    (* add successors to dag *)
    let dag = List.fold_left (fun dag x -> dag_add' x dag) dag successors in
    (* add x as predecessor to each successor *)
    let add_pred edges s =
      match SVM.find_opt s edges with
      | None -> failwith "do_add: missing node successor"
      | Some (ps, ss) -> SVM.add s (SVS.add x ps, ss) edges
    in
    { nodes = x :: dag.nodes;
      edges = List.fold_left add_pred dag.edges successors
        |> SVM.add x (SVS.empty, SVS.of_list successors);
      roots = SVS.add x dag.roots; }

let dag_add : type a. a sym_value -> dag -> dag =
  fun v dag -> dag_add' (ex_of_sym_value v) dag

(* fold in toposort order *)
let dag_fold_left f v dag =
  let do_one v node =
    match SVM.find_opt node dag.edges with
    | None ->
      failwith "dag_fold_left got nonexistent node"
    | Some (preds, succs) ->
      f node (preds, succs) v
  in
  List.fold_left do_one v dag.nodes

(* fold in reverse toposort order *)
let dag_fold_right f v dag =
  let do_one node v =
    match SVM.find_opt node dag.edges with
    | None ->
      failwith "dag_fold_right got nonexistent node"
    | Some (preds, succs) ->
      f node (preds, succs) v
  in
  List.fold_right do_one dag.nodes v

(* merge two DAGs *)
(* is there a faster algorithm? *)
let dag_merge dag1 dag2 =
  (* add each node in dag1 to dag2 *)
  let add_one x (p, s) dag' =
    match SVM.find_opt x dag'.edges with
    | None ->
      { dag' with
        nodes = x :: dag'.nodes;
        edges = SVM.add x (p, s) dag'.edges }
    | Some (p', s') ->
      if not (SVS.equal s s') then
        failwith "merge got inequal successor node sets"
      else
        { dag' with
          nodes = dag'.nodes;
          edges = SVM.add x (SVS.union p p', s) dag'.edges }
  in
  let dag = dag_fold_right add_one dag2 dag1 in
  { dag with roots = SVS.union dag1.roots dag2.roots }
