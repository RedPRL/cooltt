open Basis
open Core
open Frontend

open CodeUnit
open DriverMessage

module CS = ConcreteSyntax
module ST = RefineState
module Env = RefineEnv
module RM = RefineMonad
open Monad.Notation (RM)

open Lsp.Types

(* State *)

type state = { refiner_state : RefineState.t;
               refiner_env : RefineEnv.t;
               diagnostics : Diagnostic.t list
             }

let diagnostic severity info message =
  match Option.map Pos.located info with
  | Some range -> Diagnostic.create ~range ~severity ~message ()
  | None -> failwith "[FIXME] Basis.Basis.diagnostic: Handle missing locations"

(* Effects *)

(** Lift a refiner computation into an LWT promise. *)
let lift_rm (st : state) (m : 'a RM.m) : ('a * state) Lwt.t =
  st |> Lwt.wrap1 @@ fun st ->
  RM.run_exn st.refiner_state st.refiner_env @@
  let* r = m in
  let+ refiner_state = RM.get in
  r, { st with refiner_state }

let lift_rm_ st m =
  Lwt.map snd (lift_rm st m)

(* Actions *)

(** Parse a file. *)
let parse_file (path : string) =
  path |> Lwt.wrap1 @@ fun path ->
  (* FIXME: proper error handling here *)
  Result.get_ok @@ Load.load_file (`File path)

(** Elaborate a single definition. *)
let elab_definition (st : state) (name : Ident.t) (args : CS.cell list) (tp : CS.con) (def : CS.con) =
  lift_rm_ st @@
  let* (tp, tm) = Elaborator.elaborate_typed_term (Ident.to_string name) args tp def in
  let+ _ = RM.add_global name tp (Some tm) in
  ()

(* NOTE: Maybe it makes sense to rethink how messaging works *)
let print_ident (st : state) (ident : Ident.t CS.node) =
  let action =
    let* x = RM.resolve ident.node in
    match x with
    | `Global sym ->
      let* vtp, con = RM.get_global sym in
      let* tp = RM.quote_tp vtp in
      let* tm =
        match con with
        | None -> RM.ret None
        | Some con ->
          let* tm = RM.quote_con vtp con in
          RM.ret @@ Some tm
      in
      (* [TODO: Reed M, 24/11/2021] Rethink messaging? *)
      let msg = Format.asprintf "%a"
          pp_message @@ OutputMessage (Definition { ident = ident.node; tp; tm })
      in
      RM.ret @@ diagnostic DiagnosticSeverity.Information ident.info msg
    | _ ->  RM.ret @@ diagnostic DiagnosticSeverity.Error ident.info "Unbound identifier"
  in
  lift_rm st action |> Lwt.map @@ fun (d, st) -> { st with diagnostics = d::st.diagnostics }

(* FIXME: Handle the rest of the commands *)
let elab_decl (st : state) (decl : CS.decl) =
  match decl with
  | CS.Def { name; args; def = Some def; tp } ->
    elab_definition st name args tp def
  | CS.Print ident ->
    print_ident st ident
  | _ -> Lwt.return st

let elaborate_file (lib : Bantorra.Manager.library) (path : string) : Diagnostic.t list Lwt.t =
  let open LspLwt.Notation in
  let* sign = parse_file path in
  let elab_queue = JobQueue.create () in
  let worker = JobQueue.worker elab_queue in
  let unit_id = CodeUnitID.file path in
  (* [TODO: Reed M, 24/11/2021] I don't love how the code unit stuff works here, perhaps it's time to rethink? *)
  let refiner_state = ST.init_unit unit_id @@ ST.init worker in
  let refiner_env = Env.set_current_unit_id unit_id (Env.init lib) in
  let diagnostics = [] in
  let* st = Lwt_list.fold_left_s elab_decl { refiner_state; refiner_env; diagnostics } sign in
  Lwt.return st.diagnostics
