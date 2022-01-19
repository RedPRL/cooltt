open Core
open Basis

open CodeUnit

module S = Syntax
module D = Domain

module Sem = Semantics
module TB = TermBuilder

module Env = RefineEnv
module RM = RefineMonad
open Monad.Notation (RM)
module RMU = Monad.Util (RM)

(** Testing Utilities *)
let library_manager =
  match Bantorra.Manager.init ~anchor:"cooltt-lib" ~routers:[] with
  | Ok ans -> ans
  | Error (`InvalidRouter msg) -> failwith msg (* this should not happen! *)

let current_lib =
  match Bantorra.Manager.load_library_from_cwd library_manager with
  | Error (`InvalidLibrary err) -> failwith err
  | Ok (lib, _) -> lib

let bind_axiom (id : string) (tp : S.tp) : S.t RM.m =
  let* vtp = RM.lift_ev @@ Sem.eval_tp tp in
  let+ sym = RM.add_global (`User [id]) vtp None in
  S.Global sym

(** Check that two terms of type {mtp} are convertible in under a list of {axioms}. *)
let check_tm (axioms : (string * S.tp) list) (mtp : D.tp RM.m) : (S.t list -> D.con RM.m) Alcotest.testable =
  let state = RefineState.init_unit CodeUnitID.top_level @@ RefineState.init in
  let env = RefineEnv.init current_lib in
  let pp fmt m =
    let tm = RM.run state env @@
      let* tp = mtp in
      let* globals = RMU.map (fun (str, tp) -> bind_axiom str tp) axioms in
      let* v = m globals in
      RM.quote_con tp v
    in
    match tm with
    | Ok tm -> S.pp Pp.Env.emp fmt tm
    | Error err -> Format.fprintf fmt "Error: %s" (Printexc.to_string err)
  in
  Alcotest.testable pp @@ fun m0 m1 ->
  let res =
    RM.run state env @@
    let* tp = mtp in
    let* globals = RMU.map (fun (str, tp) -> bind_axiom str tp) axioms in
    let* v0 = m0 globals in
    let* v1 = m1 globals in
    RM.lift_conv_ @@ Conversion.equate_con tp v0 v1
  in
  match res with
  | Ok _ -> true
  | Error (Conversion.ConversionError err) ->
    (* [TODO: Reed M, 18/01/2022] Register some exception printers instead. *)
    Format.printf "Conversion Failed: %a@." Conversion.Error.pp err;
    false
  | Error _ ->
    false

module Desc =
struct
  (** Construct an nary operation. *)
  let rec nary n =
    if n = 0 then S.DescEnd else S.DescRec (nary @@ n - 1)

  let data ctx =
    S.Tm (ctx, S.DescEnd)

  let code_data ctx =
    S.CodeTm (ctx, S.DescEnd)
end

module Signature =
struct
  (** Construct a signature from a list of constructors. *)
  let of_list xs =
    List.fold_left (fun sign (lbl, t) -> S.CtxSnoc (sign, `User [lbl], t)) S.CtxNil xs
end

(** Nat Tests *)
let nat_signature : S.t =
  Signature.of_list [("z", Desc.nary 0); ("s", Desc.nary 1)]

let nat_method_tp =
  let* vnat_sig = RM.lift_ev @@ Sem.eval nat_signature in
  RM.lift_cmp @@
  Sem.splice_tp @@
  Splice.con vnat_sig @@ fun nat_sig ->
  Splice.term @@
  TB.pi (TB.tm nat_sig (TB.desc_rec TB.desc_end)) @@ fun _ -> TB.univ

let nat_mot =
  S.Pi (Desc.data nat_signature, `Machine "x", S.Univ)

let nat_zero_method () =
  let mthd [mot] =
    RM.lift_ev @@ Sem.eval @@ S.DescMethod (nat_signature, mot, Desc.nary 0)
  in
  let expected [mot] =
    let* vmot = RM.lift_ev @@ Sem.eval mot in
    RM.lift_cmp @@
    Sem.splice_tm @@
    Splice.con vmot @@ fun mot ->
    Splice.term @@
    TB.lam @@ fun z ->
    TB.ap mot [z]
  in
  Alcotest.check (check_tm ["mot", nat_mot] nat_method_tp) "method of induction for nat/zero" expected mthd

let nat_suc_method () =
  let mthd [mot] =
    RM.lift_ev @@ Sem.eval @@ S.DescMethod (nat_signature, mot, Desc.nary 1)
  in
  let expected [mot] =
    let* vmot = RM.lift_ev @@ Sem.eval mot in
    let* nat_sig = RM.lift_ev @@ Sem.eval nat_signature in
    RM.lift_cmp @@
    Sem.splice_tm @@
    Splice.con nat_sig @@ fun nat_sig ->
    Splice.con vmot @@ fun mot ->
    Splice.term @@
    TB.lam ~ident:(`User ["s"]) @@ fun s ->
    TB.code_pi (TB.code_data nat_sig) @@ TB.lam ~ident:(`User ["n"]) @@ fun n ->
    TB.code_pi (TB.ap mot [n]) @@ TB.lam @@ fun _ ->
    TB.ap mot [TB.tm_rec TB.desc_end s n]
  in
  Alcotest.check (check_tm ["mot", nat_mot] nat_method_tp) "method of induction for nat/suc" expected mthd

(** Tree Tests *)
let tree_signature : S.t =
  Signature.of_list [("leaf", Desc.nary 0); ("node", Desc.nary 2)]

let tree_method_tp =
  let* vtree_sig = RM.lift_ev @@ Sem.eval tree_signature in
  RM.lift_cmp @@
  Sem.splice_tp @@
  Splice.con vtree_sig @@ fun tree_sig ->
  Splice.term @@
  TB.pi (TB.tm tree_sig (TB.desc_rec @@ TB.desc_rec TB.desc_end)) @@ fun _ -> TB.univ

let tree_node_method () =
  let mot = S.Pi (Desc.data tree_signature, `Machine "x", S.Univ) in
  let mthd [mot] =
    RM.lift_ev @@ Sem.eval @@ S.DescMethod (tree_signature, mot, Desc.nary 2)
  in
  let expected [mot] =
    let* vmot = RM.lift_ev @@ Sem.eval mot in
    let* tree_sig = RM.lift_ev @@ Sem.eval tree_signature in
    RM.lift_cmp @@
    Sem.splice_tm @@
    Splice.con tree_sig @@ fun tree_sig ->
    Splice.con vmot @@ fun mot ->
    Splice.term @@
    TB.lam @@ fun node ->
    TB.code_pi (TB.code_data tree_sig) @@ TB.lam @@ fun t0 ->
    TB.code_pi (TB.ap mot [t0]) @@ TB.lam @@ fun _ ->
    TB.code_pi (TB.code_data tree_sig) @@ TB.lam @@ fun t1 ->
    TB.code_pi (TB.ap mot [t1]) @@ TB.lam @@ fun _ ->
    TB.ap mot [TB.tm_rec TB.desc_end (TB.tm_rec (TB.desc_rec TB.desc_end) node t0) t1]
  in
  Alcotest.check (check_tm ["mot", mot] tree_method_tp) "method of induction for tree/node" expected mthd

let () =
  let open Alcotest in
  run "Inductives" [
    "Methods of Induction", [
      test_case "nat/zero" `Quick nat_zero_method;
      test_case "nat/suc" `Quick nat_suc_method;
      test_case "tree/node" `Quick tree_node_method;
    ]
  ]
