open Basis
open Core
open Frontend

open CodeUnit

module S = Syntax
module D = Domain

module Sem = Semantics
module TB = TermBuilder

module T = Tactic
module R = Refiner
module Elab = Elaborator
module RM = RefineMonad

module Env = RefineEnv
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

(** Add an axiom to the current testing context. *)
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
