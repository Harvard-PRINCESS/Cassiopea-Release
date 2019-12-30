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

open Monad
open Value

(* type definitions for evaluation *)

module Config(V : Value) = struct
  type casp = Reps.casp_file

  (* typed values *)
  type value =
  | ValInt  of V.t_int
  | ValBool of V.t_bool
  | ValWord of V.t_word * int (* length *)
  | ValLoc  of V.t_loc * int (* length *)
  | ValStr  of string

  (* machine description and exec configuration *)
  type config = {
    c : casp;
    top : value SM.t;
    env : value SM.t;
    reg : (V.t_word * int) SM.t;
    mem : (int * int * V.t_word BM.t) SM.t;
    ctx : V.t_ctx;
    jmp : V.t_int;
  }

  (* printers *)
  let string_of_value : value -> string =
    function
    | ValInt i -> V.string_of V.IsInt i
    | ValBool b -> V.string_of V.IsBool b
    | ValWord (h, l) -> V.string_of (V.IsWord l) h
    | ValLoc (s, l) -> V.string_of (V.IsLoc l) s
    | ValStr s -> "\""^s^"\""

  let string_of_reg reg =
    let pair_to_string (k, (v, l)) =
      k^" : "^(V.string_of (V.IsWord l) v)^" : "^(string_of_int l)^" len"
    in
    SM.bindings reg
    |> List.map pair_to_string
    |> String.concat "\n"

  let string_of_mem mem =
    let string_of_region (k, (l, n, region)) =
      let pair_to_string (i, v) =
        "\t"^(string_of_int (Bits.to_int i))^" ("^
        (Bits.to_hexstring i)^") : "^(V.string_of (V.IsWord l) v)
      in
      "REGION "^k^" with "^
      (string_of_int l)^" len, "^
      (string_of_int n)^" size :\n"^
      (region
      |> BM.bindings
      |> List.map pair_to_string
      |> String.concat "\n")
    in
    SM.bindings mem
    |> List.map string_of_region
    |> String.concat "\n"

  let string_of_config conf =
    "MEMORY:\n============\n"^(string_of_mem conf.mem)^"\n"^
    "REGISTERS:\n============\n"^(string_of_reg conf.reg)^"\n"^
    "CONTEXT:\n============\n"^(V.ctx_to_string conf.ctx)^"\n"^
    "NEXT PC:\n============\n"^(V.string_of V.IsInt conf.jmp)

  (* monads *)
  type 'a stateful = config -> ('a, Pos.t * string) result
  type 'a emonad = ('a * V.t_ctx) stateful
  type smonad = config stateful

  (* converting bitvec/bitptr to word *)
  (* these stay within fallible *)
  let word_of_vec m l ctx =
    match m ctx with
    | Ok (v, ctx) -> Ok (V.lift_word (V.BitVec v) l, ctx)
    | Error s -> Error s

  let word_of_ptr m l ctx =
    match m ctx with
    | Ok (v, ctx) -> Ok (V.lift_word (V.BitPtr v) l, ctx)
    | Error s -> Error s

  (* calling value domain ops that cannot fail *)
  (* intuitively: wrap ret to get expr monad *)
  let ok_int m conf = Ok (ValInt m, conf.ctx)
  let ok_bool m conf = Ok (ValBool m, conf.ctx)
  let ok_word m l conf = Ok (ValWord (m, l), conf.ctx)
  let ok_loc m l conf = Ok (ValLoc (m, l), conf.ctx)
  let ok_string s conf = Ok (ValStr s, conf.ctx)

  (* calling value domain ops that can fail *)
  (* intuitively: wrap fallible to get expr monad *)
  let get_int pos m conf =
    match m conf.ctx with
    | Ok (v, ctx) -> Ok (ValInt v, ctx)
    | Error s -> Error (pos, s)

  let get_bool pos m conf =
    match m conf.ctx with
    | Ok (v, ctx) -> Ok (ValBool v, ctx)
    | Error s -> Error (pos, s)

  let get_word pos m l conf =
    match m conf.ctx with
    | Ok (v, ctx) -> Ok (ValWord (v, l), ctx)
    | Error s -> Error (pos, s)

  let get_loc pos m l conf =
    match m conf.ctx with
    | Ok (v, ctx) -> Ok (ValLoc (v, l), ctx)
    | Error s -> Error (pos, s)

  (* intuitively: wrap fallible to get stmt monad *)
  let get pos m conf =
    match m conf.ctx with
    | Ok ((), ctx) -> Ok { conf with ctx = ctx }
    | Error s -> Error (pos, s)

  (* expression evaluation monad *)
  (* config -> (value, Pos.t * string) result * V.t_ctx *)
  (* the final result might be another monad, e.g. the statement monad *)

  let returnE a conf = Ok (a, conf.ctx)

  let bindE m k conf =
    match m conf with
    | Error e -> Error e
    | Ok (v, ctx) ->
      let conf = { conf with ctx = ctx } in
      k v conf

  let bindE2 m1 m2 k conf =
    match m1 conf with
    | Error e -> Error e
    | Ok (v1, ctx) ->
      let conf = { conf with ctx = ctx } in
      match m2 conf with
      | Error e -> Error e
      | Ok (v2, ctx) ->
        let conf = { conf with ctx = ctx } in
        k (v1, v2) conf

  let bindE3 m1 m2 m3 k conf =
    match m1 conf with
    | Error e -> Error e
    | Ok (v1, ctx) ->
      let conf = { conf with ctx = ctx } in
      match m2 conf with
      | Error e -> Error e
      | Ok (v2, ctx) ->
        let conf = { conf with ctx = ctx } in
        match m3 conf with
        | Error e -> Error e
        | Ok (v3, ctx) ->
          let conf = { conf with ctx = ctx} in
          k (v1, v2, v3) conf

  (* a special bind for changing the environment *)
  let bindE_let i m k conf =
    let env = conf.env in
    match m conf with
    | Error e -> Error e
    | Ok (v, ctx) ->
      let conf = { conf with env = SM.add i v env; ctx = ctx } in
      k conf

  let mergeE do_merge b m1 m2 conf =
    let conf = { conf with ctx = V.ctx_branch conf.ctx } in
    match (m1 conf, m2 conf) with
    | (Ok (v1, ctx1), Ok (v2, ctx2)) ->
      let ctx = V.ctx_merge b ctx1 ctx2 in
      Ok (do_merge b v1 v2, ctx)
    | (Ok (v, ctx), Error (pos, s)) ->
      let ctx = V.ctx_unbranch ctx in
      begin match V.assert_ "" b ctx with
      | Ok ((), ctx) -> Ok (v, ctx)
      | Error _ -> Error (pos, s)
      end
    | (Error (pos, s), Ok (v, ctx)) ->
      let ctx = V.ctx_unbranch ctx in
      begin match V.assert_ "" (V.log_not b) ctx with
      | Ok ((), ctx) -> Ok (v, ctx)
      | Error _ -> Error (pos, s)
      end
    | (Error _, Error _) ->
      Error (Pos.none, "ife double failure")

  (* statement evaluation monad *)
  (* config -> (config, Pos.t * string) result *)
  (* the final result might be another monad *)

  let returnS conf = Ok conf

  let bindS m k conf =
    match m conf with
    | Ok conf -> k conf
    | Error e -> Error e

  (* a special bind for changing the environment *)
  (* restores the original environment after evaluation *)
  let bindS_env env' k conf =
    let env = conf.env in
    let conf = { conf with env = env' } in
    match k conf with
    | Error e -> Error e
    | Ok conf -> Ok { conf with env = env }

  (* merge two stmt monads under branch condition b *)
  let mergeS do_merge b m1 m2 conf =
    let conf = { conf with ctx = V.ctx_branch conf.ctx } in
    match (m1 conf, m2 conf) with
    | (Ok conf1, Ok conf2) ->
      Ok (do_merge b conf1 conf2)
    | (Ok conf, Error (pos, s)) ->
      let ctx = V.ctx_unbranch conf.ctx in
      begin match V.assert_ "" b ctx with
      | Ok ((), ctx) -> Ok { conf with ctx = ctx }
      | Error _ -> Error (pos, s)
      end
    | (Error (pos, s), Ok conf) ->
      let ctx = V.ctx_unbranch conf.ctx in
      begin match V.assert_ "" (V.log_not b) ctx with
      | Ok ((), ctx) -> Ok { conf with ctx = ctx }
      | Error _ -> Error (pos, s)
      end
    | (Error _, Error _) ->
      get Pos.none (error "mergeS double failure") conf

  (* map a function (string * int -> V.t_word -> 'a) across registers *)
  let reg_map f reg =
    let app_one i (v, l) =
      (f (i, l) v, l)
    in
    SM.mapi app_one reg

  (* map a function (string * int * int -> int -> V.t_word -> 'a) across memories *)
  let mem_map f mem =
    let region_map i (l, n, m) =
      (l, n, BM.mapi (f (i, l, n)) m)
    in
    SM.mapi region_map mem

  (* like map merge, but for register sets *)
  let reg_merge f reg1 reg2 =
    let merge_one i r1 r2 =
      match (r1, r2) with
      | (Some (v1, l1), Some (v2, l2)) ->
        if l1 <> l2 then
          failwith ("ERROR: register "^i^" "^
                    "got different-length bitvectors: "^
                    "got "^(string_of_int l1)^" and "^(string_of_int l2))
        else
          Some (f i l1 v1 v2)
      | _ ->
        failwith ("ERROR: missing register "^i)
    in
    SM.merge merge_one reg1 reg2

  (* like map merge, but for memories *)
  let mem_merge f mem1 mem2 =
    let merge_region i m1 m2 =
      let merge_one l o v1 v2 =
        match (v1, v2) with
        | (Some v1, Some v2) ->
          Some (f i o l v1 v2)
        | _ ->
          failwith ("ERROR: memory region "^i^" "^
                    "is missing offset "^(string_of_int (Bits.to_int o)))
      in
      match (m1, m2) with
      | (Some (l1, n1, m1), Some (l2, n2, m2)) ->
        if l1 <> l2 || n1 <> n2 then
          failwith ("ERROR: memory region "^i^" "^
                    "got differing types: "^
                    (string_of_int l1)^" bit, "^
                    (string_of_int n1)^" len vs. "^
                    (string_of_int l2)^" bit, "^
                    (string_of_int n2)^" len")
        else
          Some (l1, n1, BM.merge (merge_one l1) m1 m2)
      | _ ->
        failwith ("ERROR: missing memory region "^i)
    in
    SM.merge merge_region mem1 mem2

  (* registers(expr monad) -> expr monad(registers) *)
  let reg_flatten reg =
    let flatten_one i (v, l) reg =
      bind2 v reg (fun (v, reg) -> ok (SM.add i (v, l) reg))
    in
    SM.fold flatten_one reg (ok SM.empty)

  (* memory(expr monad) -> expr monad(memory) *)
  let mem_flatten mem =
    let flatten_region i (l, n, m) mem =
      let flatten_one o v m =
        bind2 v m (fun (v, m) -> ok (BM.add o v m))
      in
      bind2 (BM.fold flatten_one m (ok BM.empty)) mem
      (fun (m, mem) -> ok (SM.add i (l, n, m) mem))
    in
    SM.fold flatten_region mem (ok SM.empty)

  let val_merge pos b v1 v2 =
    match (v1, v2) with
    | (ValInt v1, ValInt v2) ->
      ValInt (V.ife V.IsInt b v1 v2)
    | (ValBool v1, ValBool v2) ->
      ValBool (V.ife V.IsBool b v1 v2)
    | (ValWord (v1, l1), ValWord (v2, l2)) ->
      if l1 <> l2 then
        failat pos "type error: different bitvector lengths in ife"
      else
        ValWord (V.ife (V.IsWord l1) b v1 v2, l1)
    | (ValLoc (v1, l1), ValLoc (v2, l2)) ->
      if l1 <> l2 then
        failat pos "type error: different loc lengths in ife"
      else
        ValLoc (V.ife (V.IsLoc l1) b v1 v2, l1)
    | (ValStr s1, ValStr s2) ->
      if V.lower_bool b then
        ValStr s1
      else
        ValStr s2
    | (_, _) ->
      failat pos "type error: ife branches with differing types"

  let conf_merge b conf1 conf2 =
    if conf1.c != conf2.c then
      failwith "conf_merge: configs have different casps"
    else if conf1.top != conf2.top then
      failwith "conf_merge: configs have different tops"
    else if conf1.env != conf2.env then
      failwith "conf_merge: configs have different envs"
    else
    { c = conf1.c;
      top = conf1.top;
      env = conf1.env;
      reg = reg_merge
        (fun _ l v1 v2 -> (V.ife (V.IsWord l) b v1 v2, l))
        conf1.reg conf2.reg;
      mem = mem_merge
        (fun _ _ l v1 v2 -> V.ife (V.IsWord l) b v1 v2)
        conf1.mem conf2.mem;
      ctx = V.ctx_merge b conf1.ctx conf2.ctx;
      jmp = V.ife V.IsInt b conf1.jmp conf2.jmp; }
end
