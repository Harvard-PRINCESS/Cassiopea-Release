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
open Symexec
open Query

(* dependency analysis *)

(* mapping variables to bitvector offsets *)
type offsets = {
  int_off : int IM.t;
  bool_off : int IM.t;
  vec_off : int IM.t;
  width : int;
}

let string_of_offsets off =
  let pair_to_string (i, o) =
    (string_of_int i)^":"^(string_of_int o)
  in
  let int_str =
    IM.bindings off.int_off
    |> List.map pair_to_string
    |> String.concat " "
  in
  let bool_str =
    IM.bindings off.bool_off
    |> List.map pair_to_string
    |> String.concat " "
  in
  let vec_str =
    IM.bindings off.vec_off
    |> List.map pair_to_string
    |> String.concat " "
  in
  "WIDTH: "^(string_of_int off.width)^"\n"^
  "INTS: "^int_str^"\n"^
  "BOOLS: "^bool_str^"\n"^
  "VECS: "^vec_str

(* get an assignment of bitvector offsets to variables *)
(* conveniently happens to be deterministic *)
let offsets_of_vars vars =
  let count = ref 0 in
  let add_off i map =
    let map = IM.add i !count map in
    count := !count + 1; map
  in
  let int_off = IS.fold add_off vars.int_set IM.empty in
  let bool_off = IS.fold add_off vars.bool_set IM.empty in
  let vec_off = IM.fold (fun i _ -> add_off i) vars.vec_set IM.empty in
  let count = !count in
  { int_off = int_off;
    bool_off = bool_off;
    vec_off = vec_off;
    width = count; }

let offsets_mem_int off i =
  match IM.find_opt i off.int_off with
  | Some o -> Bits.set (Bits.zero off.width) (bint_of_int o)
  | None -> failwith ("offsets_mem: no offset for int "^(string_of_int i))

let offsets_mem_bool off i =
  match IM.find_opt i off.bool_off with
  | Some o -> Bits.set (Bits.zero off.width) (bint_of_int o)
  | None -> failwith ("offsets_mem: no offset for bool "^(string_of_int i))

let offsets_mem_vec off i =
  match IM.find_opt i off.vec_off with
  | Some o -> Bits.set (Bits.zero off.width) (bint_of_int o)
  | None -> failwith ("offsets_mem: no offset for vec "^(string_of_int i))

(* get bv representation of var set *)
let offsets_mem off vars =
  let mem_int i deps = Bits.or_ (offsets_mem_int off i) deps in
  let mem_bool i deps = Bits.or_ (offsets_mem_bool off i) deps in
  let mem_vec i _ deps = Bits.or_ (offsets_mem_vec off i) deps in
  Bits.zero off.width
  |> IS.fold mem_int vars.int_set
  |> IS.fold mem_bool vars.bool_set
  |> IM.fold mem_vec vars.vec_set

(* INPUT DEPENDENCIES *)

type depends = {
  off : offsets;
  reg : bits SM.t;
  mem : bits BM.t SM.t;
}

let string_of_depends (depends : depends) =
  let reg_string =
    SM.bindings depends.reg
    |> List.map (fun (i, v) -> i^":"^(Bits.to_bitstring v))
    |> String.concat "\n"
  in
  "OFFSETS:\n"^(string_of_offsets depends.off)^"\n"^
  "REG:\n"^reg_string

(* test univalence of v *)
let univalence_of_value spec (v : word sym_value) =
  let evars = evars_of_spec spec in
  let vars = vars_of_sym_value v in
  let refresh = model_refresh (vars_inter evars vars) in

  let cond = spec.pre.pure
    |> log_and spec.post.pure
    |> log_and (subst refresh spec.post.pure)
    |> log_and (log_not (eq_word v (subst refresh v)))
  in
  match esolve cond with
  | Some _ -> false
  | None -> true

(* test dependency of v on each variable in vars *)
(* results encoded as a vector according to off *)
let depends_of_value off (spec : sspec) (v : word sym_value) =
  let avars = avars_of_spec spec in
  let evars = evars_of_spec spec in
  let vars = vars_of_sym_value v in

  (* evar refresh model *)
  let refresh = model_refresh (vars_inter evars vars) in

  (* test deps on variable(s) replaced by diff *)
  let check_depend diff =
    (* find variable assignments satisfying pure precond *)
    (* with possibly different values from diff *)
    (* to cause this location's value to differ *)
    let cond = spec.pre.pure
      |> log_and spec.post.pure
      |> log_and (spec.pre.pure |> subst diff)
      |> log_and (spec.post.pure |> subst diff |> subst refresh)
      |> log_and (log_not (eq_word v (v |> subst diff |> subst refresh)))
    in
    match esolve cond with
    | Some _ -> true
    | None -> false
  in

  let int_depend i deps =
    let diff = model_add_int i (next_sym_int ()) model_empty in
    if check_depend diff then
      Bits.or_ deps (offsets_mem_int off i)
    else deps
  in
  let bool_depend i deps =
    let diff = model_add_bool i (next_sym_bool ()) model_empty in
    if check_depend diff then
      Bits.or_ deps (offsets_mem_bool off i)
    else deps
  in
  let vec_depend i l deps =
    let diff = model_add_vec i (next_sym_vec l) model_empty in
    if check_depend diff then
      Bits.or_ deps (offsets_mem_vec off i)
    else deps
  in

  if univalence_of_value spec v then
    (* test deps on every universally quantified variable *)
    (* if it's all universals, then only test on those *)
    let test_vars =
      if vars_is_empty (vars_diff vars avars) then
        vars_inter vars avars
      else avars
    in
    Some (Bits.zero off.width
      |> IS.fold int_depend test_vars.int_set
      |> IS.fold bool_depend test_vars.bool_set
      |> IM.fold vec_depend test_vars.vec_set)
  else
    None

(* analyze dependencies of spec postcond elements *)
(* run this on the unframed spec for no-modify constraints *)
let depends_of_spec (spec : sspec) : depends =
  (* convert avars to mapping from variables to offsets *)
  let off = offsets_of_vars (avars_of_spec spec) in

  (* measure dependencies for each postcond location *)
  let reg_depends i (v, _) reg =
    match depends_of_value off spec v with
    | Some deps -> SM.add i deps reg
    | None -> reg
  in
  let mem_depends i (_, _, region) mem =
    let region_depends o v region =
      match depends_of_value off spec v with
      | Some deps -> BM.add o deps region
      | None -> region
    in
    let res = BM.fold region_depends region BM.empty in
    if not (BM.is_empty res) then
      SM.add i res mem
    else mem
  in

  { off = off;
    reg = SM.fold reg_depends spec.post.reg SM.empty;
    mem = SM.fold mem_depends spec.post.mem SM.empty; }

(* SYMBOLIC VALUE DEPENDENCIES *)

type 'a maydepend =
| Control of 'a sym_value (* a value only depending on control vars *)
| Input of bits sym_value (* a value depending on control and/or input vars *)

(* ocaml doesn't support better polymorphism so here we are *)
type memo_maydepend = {
  int_mdmap : bint maydepend IntWSM.t;
  bool_mdmap : bool maydepend BoolWSM.t;
  loc_mdmap : id maydepend LocWSM.t;
  vec_mdmap : bits maydepend VecWSM.t;
  ptr_mdmap : (id * bits sym_value) maydepend PtrWSM.t;
  word_mdmap : word_t maydepend WordWSM.t;
}

let mk_memo_maydepend () = {
  int_mdmap = IntWSM.create 251;
  bool_mdmap = BoolWSM.create 251;
  loc_mdmap = LocWSM.create 251;
  vec_mdmap = VecWSM.create 251;
  ptr_mdmap = PtrWSM.create 251;
  word_mdmap = WordWSM.create 251;
}

let memo_maydepend_mem :
  type a. memo_maydepend ->
    a sym_value ->
    a maydepend option =
  fun memo v ->
  match typ_of_sym_value v with
  | IsInt -> IntWSM.find_opt memo.int_mdmap v
  | IsBool -> BoolWSM.find_opt memo.bool_mdmap v
  | IsLoc _ -> LocWSM.find_opt memo.loc_mdmap v
  | IsVec _ -> VecWSM.find_opt memo.vec_mdmap v
  | IsPtr _ -> PtrWSM.find_opt memo.ptr_mdmap v
  | IsWord _ -> WordWSM.find_opt memo.word_mdmap v

let memo_maydepend_add :
  type a. memo_maydepend ->
    a sym_value ->
    a maydepend ->
    a maydepend =
  fun memo v md ->
  match memo_maydepend_mem memo v with
  | Some md' ->
    begin match (md, md') with
    | (Control v1, Control v2) when v1.tag <> v2.tag ->
      failwith "memo_maydepend_add: double add with different values!"
    | (Input v1, Input v2) when v1.tag <> v2.tag ->
      failwith "memo_maydepend_add: double add with different values!"
    | _ -> md'
    end
  | None ->
  begin match typ_of_sym_value v with
  | IsInt -> IntWSM.add memo.int_mdmap v md
  | IsBool -> BoolWSM.add memo.bool_mdmap v md
  | IsLoc _ -> LocWSM.add memo.loc_mdmap v md
  | IsVec _ -> VecWSM.add memo.vec_mdmap v md
  | IsPtr _ -> PtrWSM.add memo.ptr_mdmap v md
  | IsWord _ -> WordWSM.add memo.word_mdmap v md
  end; md

let input_of_maydepend off : 'a maydepend -> bits sym_value =
  function
  | Control _ -> mk_vec (Bits.zero off.width)
  | Input v -> v

let maydepend_of_sym_value' :
  type a. memo_maydepend -> vars -> offsets ->
    a sym_value -> bits sym_value =
  fun memo avars offs v ->
  let zero = mk_vec (Bits.zero offs.width) in
  let rec do_maydepend :
    type a.
      a sym_value ->
      a maydepend =
    fun v ->
    match memo_maydepend_mem memo v with
    | Some maydepend -> maydepend
    | None -> memo_maydepend_add memo v
      begin let vars = vars_of_sym_value v in
      if vars_is_empty (vars_diff vars avars) then
        Input (mk_vec (offsets_mem offs vars))
      else if vars_is_empty (vars_inter vars avars) then
        Control v
      else
        match v.node with
        | SymVal (IsPtr l, (i, o)) ->
          begin match do_maydepend o with
          | Control v -> Control (mk_ptr (i, v) l)
          | Input v -> Input v
          end
        | SymVal (IsWord l, BitVec v) ->
          begin match do_maydepend v with
          | Control v -> Control (mk_word (BitVec v) l)
          | Input v -> Input v
          end
        | SymVal (IsWord l, BitPtr p) ->
          begin match do_maydepend p with
          | Control v -> Control (mk_word (BitPtr v) l)
          | Input v -> Input v
          end
        | SymUnop (u, v) ->
          let v = do_maydepend v in
          begin match v with
          | Control v -> Control (mk_unop u v)
          | Input v -> Input v
          end
        | SymBinop (b, v1, v2) ->
          let v1 = do_maydepend v1 in
          let v2 = do_maydepend v2 in
          begin match (v1, v2) with
          | (Control v1, Control v2) ->
            Control (mk_binop b v1 v2)
          | (Input v1, Input v2) ->
            Input (bit_or v1 v2)
          | (Control v1, Input v2) ->
            begin match b with
            | LogAnd -> Input (mk_ite v1 v2 zero)
            | LogOr -> Input (mk_ite v1 zero v2)
            | _ -> Input v2
            end
          | (Input v1, Control v2) ->
            begin match b with
            | LogAnd -> Input (mk_ite v2 v1 zero)
            | LogOr -> Input (mk_ite v2 zero v1)
            | _ -> Input v1
            end
          end
        | SymIte (b, v1, v2) ->
          let b = do_maydepend b in
          let v1 = do_maydepend v1 in
          let v2 = do_maydepend v2 in
          begin match (b, v1, v2) with
          | (Control b, Control v1, Control v2) ->
            Control (mk_ite b v1 v2)
          | (Control b, _, _) ->
            let v1 = input_of_maydepend offs v1 in
            let v2 = input_of_maydepend offs v2 in
            Input (mk_ite b v1 v2)
          | (Input b, _, _) ->
            let v1 = input_of_maydepend offs v1 in
            let v2 = input_of_maydepend offs v2 in
            Input (bit_or b (bit_or v1 v2))
          end
        | SymMultiop (b, ls, t, k) ->
          let do_one v v' =
            match (v, v') with
            | (Control v, Control v') -> Control (mk_binop b v v')
            | (Input v, Input v') -> Input (bit_or v v')
            | (Control v, Input v') ->
              begin match b with
              | LogAnd -> Input (mk_ite v v' zero)
              | LogOr -> Input (mk_ite v zero v')
              | _ -> Input v'
              end
            | (Input v, Control v') ->
              begin match b with
              | LogAnd -> Input (mk_ite v' v zero)
              | LogOr -> Input (mk_ite v' zero v)
              | _ -> Input v
              end
          in
          List.fold_left do_one
            (Control (symbolicize t k))
            (List.rev_map do_maydepend ls)
        | SymChoose (ls, tl) ->
          let do_one v' (b, v) =
            match (b, v, v') with
            | (Control b, Control v, Control v') ->
              Control (mk_ite b v v')
            | (Control b, _, _) ->
              let v = input_of_maydepend offs v in
              let v' = input_of_maydepend offs v' in
              Input (mk_ite b v v')
            | (Input b, _, _) ->
              let v = input_of_maydepend offs v in
              let v' = input_of_maydepend offs v' in
              Input (bit_or b (bit_or v v'))
          in
          let maydepend_of_pair (b, v) = (do_maydepend b, do_maydepend v) in
          List.fold_left do_one (do_maydepend tl)
            (List.rev_map maydepend_of_pair ls)
        | _ -> failwith "impossible"
      end
  in
  input_of_maydepend offs (do_maydepend v)

let maydepend_of_sym_value :
  type a. vars -> offsets ->
    a sym_value -> bits sym_value =
  fun avars offs v ->
  maydepend_of_sym_value' (mk_memo_maydepend ()) avars offs v

type maydepends = {
  reg : bits sym_value SM.t;
  mem : bits sym_value BM.t SM.t;
}

(* turn config into universal variable may-depend vectors *)
let maydepend_of_config (avars : vars) (offs : offsets) (conf : config) =
  (* perform recursive rewrite on every location *)
  let memo = mk_memo_maydepend () in
  let reg_depend (v, _) = maydepend_of_sym_value' memo avars offs v in
  let mem_depend (_, _, region) =
    let region_depend v = maydepend_of_sym_value' memo avars offs v in
    BM.map region_depend region
  in

  { reg = SM.map reg_depend conf.reg;
    mem = SM.map mem_depend conf.mem; }

let apply_depend (dep : depends) (maydep : maydepends) =
  let reg_depend i v =
    match SM.find_opt i maydep.reg with
    | None ->
      failwith ("apply_depend: missing reg "^i)
    | Some v' ->
      eq_vec (bit_or v' (mk_vec v)) v'
  in
  let mem_depend i region =
    let region_depend region' o v =
      match BM.find_opt o region' with
      | None ->
        failwith ("apply_depend: missing mem "^i^
                  " offset "^(string_of_int (Bits.to_int o)))
      | Some v' ->
        eq_vec (bit_or v' (mk_vec v)) v'
    in
    match SM.find_opt i maydep.mem with
    | None ->
      failwith ("apply_depend: missing mem "^i)
    | Some region' ->
      let deps = BM.mapi (region_depend region') region in
      BM.fold (fun _ -> log_and) deps (mk_bool true)
  in
  let reg_deps = SM.mapi reg_depend dep.reg in
  let mem_deps = SM.mapi mem_depend dep.mem in
  log_and
  (SM.fold (fun _ -> log_and) reg_deps (mk_bool true))
  (SM.fold (fun _ -> log_and) mem_deps (mk_bool true))

let add_depends spec final term =
  if !settings.no_depend then
    term
  else
    (* calculate dependencies *)
    let start_time = Unix.gettimeofday () in
    let depends = depends_of_spec spec in
    print_log "Found dependencies in: %fs\n"
      (Unix.gettimeofday () -. start_time);
    (if !settings.debugging then
      print_log "DEPENDENCIES:\n%s\n" (string_of_depends depends));
    flush_log ();

    let start_time = Unix.gettimeofday () in
    let maydepends =
      maydepend_of_config (avars_of_spec spec) depends.off final
    in
    let deps = apply_depend depends maydepends in
    print_log "Found value dependencies in: %fs\n"
      (Unix.gettimeofday () -. start_time);
    flush_log ();

    { term with asserts = log_and deps term.asserts }
