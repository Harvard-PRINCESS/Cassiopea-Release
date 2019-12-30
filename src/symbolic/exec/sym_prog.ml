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
open Interpret
open SV
open SC
open SE
open SI

open Sym_exec
open Sym_config

(* methods for handling symbolic programs *)

(* default instruction order *)
let firstorder = [
  "memory_handle";
  "arith";
  "logic";
  "data_handle";
  "branch";
  "coprocessor"]
let lastorder = ["NoTyped"]
let sort_func_order (c: casp) order =
  let oplist = SM.bindings c.opcategory in
  let merge_subtype (k, sm) = (k, SM.fold (fun _ v s -> SS.union s v) sm SS.empty) in
  let filter_optype i =
    match List.find_opt (fun (k, _) -> k = i) oplist with
    | Some (i, sm) -> merge_subtype (i, sm)
    | None -> (i, SS.empty)
  in
  let ops_firstorder = List.map filter_optype order in
  let ops_lastorder = List.map filter_optype lastorder in
  let ops_rest =
    List.map merge_subtype (List.filter (fun (k, _) ->
                  not (List.mem k (order @ lastorder)))
    oplist)
  in
  let ops = ops_firstorder @ ops_rest @ ops_lastorder in
  let ops_rev = List.rev ops in

  let get_ops (_optype, opset) =
    let opdefs = SM.filter (fun k _v -> SS.mem k opset) c.defops in
    (* List.rev (SM.bindings opdefs) *)
    (SM.bindings opdefs)
  in
  let ops_in_order = List.map get_ops ops_rev in
  List.concat ops_in_order

let rec string_of_sym_inst =
  function
  | ConInst (i, args) ->
    "(" ^ i ^ " " ^
    (args |> (List.map string_of_value) |> String.concat " ") ^ ")"
  | SymInstIte (b, i1, i2) ->
    "(ite ("^
      (string_of_sym_value b)^") "^
      (string_of_sym_inst i1)^" "^
      (string_of_sym_inst i2)^")"

let string_of_sym_prog p = p
  |> List.map string_of_sym_inst
  |> String.concat "\n"

(* generate a symbolic instance of instruction i *)
let next_inst (c: casp) ss (i, (aa, _)) =
  (* generate next symbolic arg of type t *)
  let arg_of_type vv (_, t) =
    match vv with
    | Some vv ->
      begin match t with
      | IntType ->
        let v = next_sym_int () in Some (ValInt v :: vv)
      | BoolType ->
        let v = next_sym_bool () in Some (ValBool v :: vv)
      | BitType l ->
        let v = next_sym_word_vec l in Some (ValWord (v, l) :: vv)
      | LocType l ->
        begin match next_sym_loc c l with
        | Some v -> Some (ValLoc (v, l) :: vv)
        | None -> None
        end
      | LabelType l ->
        begin match next_sym_lbl c l with
        | Some v -> Some (ValWord (v, l) :: vv)
        | None -> None
        end
      | _ -> failwith "impossible argument type in next_sym_inst"
      end
    | None -> None
  in
  (* generate symbolic args for instruction i*)
  let vv =
    aa
    |> List.rev
    |> List.fold_left arg_of_type (Some [])
  in
  match vv with
  | Some vv ->
    begin match ss with
    | None -> Some (ConInst (i, vv))
    | Some ss ->
      let sb = next_sym_bool () in
      Some (SymInstIte (sb, ConInst (i, vv), ss))
    end
  | None -> ss (* invalid arguments, such as no label exists *)

(* generate another fully default general symbolic instruction *)
let next_sym_inst (c : casp) =
  match List.fold_left (next_inst c) None (SM.bindings c.defops) with
  | None -> failwith "no valid operation found!"
  | Some ss -> ss

(* generate another fully general symbolic instruction with sorting function *)
let next_sort_sym_inst (c : casp) sort_func order =
  let operations = sort_func c order in
  match List.fold_left (next_inst c) None operations with
  | None -> failwith "no valid operation found!"
  | Some ss -> ss

(* generate another symbolic instruction with category input *)
let next_categorized_sym_inst (c : casp) (instset: SS.t) =
  let ops =
    List.filter (fun (i, _) -> SS.mem i instset) (SM.bindings c.defops)
  in
  let ops = if will_whiten "insts" then shuffle ops else ops in
  match List.fold_left (next_inst c) None ops with
  | None -> failwith "no valid operation found!"
  | Some ss -> ss

let vars_of_t =
  function
  | ValInt d -> vars_of_sym_value d
  | ValBool b -> vars_of_sym_value b
  | ValWord (h, _l) -> vars_of_sym_value h
  | ValLoc (s, _l) -> vars_of_sym_value s
  | ValStr _ -> vars_empty

(* get symbolic variables in symbolic instruction *)
let rec vars_of_sym_inst si =
  match si with
  | ConInst (_, aa) ->
    aa
    |> List.map vars_of_t
    |> List.fold_left vars_union vars_empty
  | SymInstIte (b, i1, i2) ->
    let vb = vars_of_sym_value b in
    let vi1 = vars_of_sym_inst i1 in
    let vi2 = vars_of_sym_inst i2 in
    List.fold_left vars_union vars_empty [vb; vi1; vi2]

(* get symbolic variables in symbolic program *)
let vars_of_sym_prog sp =
  sp
  |> List.map vars_of_sym_inst
  |> List.fold_left vars_union vars_empty

let subst_t model =
  function
  | ValInt d -> ValInt (subst model d)
  | ValBool b -> ValBool (subst model b)
  | ValWord (h, l) -> ValWord (subst model h, l)
  | ValLoc (s, l) -> ValLoc (subst model s, l)
  | ValStr s -> ValStr s

(* apply substitutions in given model to a symbolic instruction *)
let rec subst_inst model =
  function
  | ConInst (i, aa) ->
    ConInst (i, List.map (subst_t model) aa)
  | SymInstIte (b, i1, i2) ->
    SymInstIte (subst model b, subst_inst model i1, subst_inst model i2)

(* apply substitutions in given model to a symbolic program *)
let subst_prog model sp =
  List.map (subst_inst model) sp

let rec simpl_inst =
  function
  | ConInst (i, aa) ->
    ConInst (i, aa)
  | SymInstIte (b, i1, i2) ->
    if b == mk_bool true then
      simpl_inst i1
    else if b == mk_bool false then
      simpl_inst i2
    else
      SymInstIte (b, i1, i2)

let simpl_prog sp =
  List.map simpl_inst sp

(* only apply inst_name substitutions in given model to a symbolic instruction *)
let rec abstract_inst model =
  function
  | ConInst (i, aa) ->
    ConInst (i, aa)
  | SymInstIte (b, i1, i2) ->
    SymInstIte (subst model b, abstract_inst model i1, abstract_inst model i2)

(* only apply inst_name substitutions in given model to a symbolic program *)
let abstract_prog model sp =
  simpl_prog (List.map (abstract_inst model) sp)

(* only apply category substitutions in given model to a symbolic program *)
let category_prog (c: casp) model sp =
  let concrete_prog = simpl_prog (subst_prog model sp) in
  let abstract_category inst =
    match inst with
    | SymInstIte _-> failwith "invalid symbolic instruction ite!"
    | ConInst (i, _) ->
      let check_subtypes _ sm = SM.fold (fun _ v b -> b || SS.mem i v) sm false in
      let insts_category = SM.filter check_subtypes c.opcategory in
      let get_subtypes _ sm ss =
        SM.fold (fun _ v s -> if SS.mem i v then SS.union s v else s) sm ss in
      let insts = SM.fold get_subtypes insts_category SS.empty in
      next_categorized_sym_inst c insts
  in
  List.map abstract_category concrete_prog

(* RELATING SYMBOLIC AND CONCRETE PROGS *)

let lift_inst c (_, (i, aa)) =
  let vv = List.map (eval_atomic c (eval_env c)) aa in
  ConInst (i, vv)

let lift_prog c p =
  List.map (lift_inst c) p

let inst_of_sketch c (pos, si) =
  match si with
  | SketchInst (i, aa) ->
    let aa_pair =
      match SM.find_opt i c.defops with
      | Some (aa', _s) -> (List.map snd aa') |> List.combine aa
      | None -> failat pos ("should not happen: unknown op "^i)
    in
    let get_args ((pos, a), t) =
      match a with
      | SketchArg a -> eval_atomic c (eval_env c) (pos, a)
      | SketchArgPlaceHolder ->
        begin match t with
        | IntType -> let v = next_sym_int () in ValInt v
        | BoolType -> let v = next_sym_bool () in ValBool v
        | BitType l -> let v = next_sym_word_vec l in ValWord (v, l)
        | LocType l ->
          begin match next_sym_loc c l with
          | Some v -> ValLoc (v, l)
          | None -> failat pos "no valid loc sketching"
          end
        | LabelType l ->
          begin match next_sym_lbl c l with
          | Some v -> ValWord (v, l)
          | None -> failat pos "no valid label sketching"
          end
        | _ -> failat pos "invalid sketching argument type "
        end
    in
    let vv = List.map get_args aa_pair in
    ConInst (i, vv)
  | SketchInstPlaceHolder -> next_sym_inst c

let prog_of_sketch c p =
  List.map (inst_of_sketch c) p

(* lower a symbolic argument to an atomic *)
let lower_t c =
  function
  | ValInt d -> Int (lower_int d)
  | ValWord (h, _) ->
    begin match (lower_word h) with
    | BitVec v -> Vec (lower_vec v)
    | BitPtr p ->
      let (i, o) = lower_ptr p in
      begin match SM.find_opt i c.mems with
      | Some (_, _, _, Some x) ->
        let o = Bits.to_big_int o in
        if BI.equal o BI.zero then Id x
        else Ptr (i, o)
      | Some _ ->
        failwith ("lower_t: region "^i^" lacks label name")
      | None ->
        failwith ("lower_t: region "^i^" not found")
      end
    end
  | ValBool b -> Bool (lower_bool b)
  | ValLoc (s, _) -> Id (lower_loc s)
  | ValStr s -> Str s

(* turn symbolic inst into concrete inst *)
let rec lower_inst c =
  function
  | ConInst (i, aa) ->
    (Pos.none, (i, List.map (fun v -> (Pos.none, lower_t c v)) aa))
  | SymInstIte (b, i1, i2) ->
    if lower_bool b then
      lower_inst c i1
    else
      lower_inst c i2

(* turn symbolic prog into concrete prog *)
let lower_prog c sp =
  List.map (lower_inst c) sp
