open Basis
open Bwd
open Frontend
open Core
open CodeUnit
open Cubical

module S = Syntax
module D = Domain
module Metadata = RefineMetadata

open Lsp.Types

module RPC = Jsonrpc
module Request = Lsp.Client_request
module Notification = Lsp.Client_notification
module Broadcast = Lsp.Server_notification
module Json = Lsp.Import.Json

type rpc_message = RPC.Id.t option RPC.Message.t
type rpc_request = RPC.Message.request
type rpc_notification = RPC.Message.notification

type 'resp request = 'resp Lsp.Client_request.t
type notification = Lsp.Client_notification.t

type hole = Hole of { ctx : (Ident.t * S.tp) list; goal : S.tp }

type server =
  { lsp_io : LspLwt.io;
    library : Bantorra.Manager.library;
    (* FIXME: We should probably thread this through. *)
    mutable should_shutdown : bool;
    mutable hover_info : string IntervalTree.t;
    mutable holes : Metadata.hole IntervalTree.t
  }

type lsp_error =
  | DecodeError of string
  | HandshakeError of string
  | ShutdownError of string
  | UnknownRequest of string
  | UnknownNotification of string

exception LspError of lsp_error

let () = Printexc.register_printer @@
  function
  | LspError (DecodeError err) -> Some (Format.asprintf "Lsp Error: Couldn't decode %s" err)
  | LspError (HandshakeError err) -> Some (Format.asprintf "Lsp Error: Invalid initialization handshake %s" err)
  | LspError (ShutdownError err) -> Some (Format.asprintf "Lsp Error: Invalid shutdown sequence %s" err)
  | LspError (UnknownRequest err) -> Some (Format.asprintf "Lsp Error: Unknown request %s" err)
  | LspError (UnknownNotification err) -> Some (Format.asprintf "Lsp Error: Unknown notification %s" err)
  | _ -> None

open LspLwt.Notation

(* Server Notifications *)
let broadcast server notif =
  let msg = Broadcast.to_jsonrpc notif in
  LspLwt.send server.lsp_io (RPC.Message { msg with id = None })

let publish_diagnostics server path (diagnostics : Diagnostic.t list) =
  let uri = DocumentUri.of_path path in
  let params = PublishDiagnosticsParams.create ~uri ~diagnostics () in
  broadcast server (PublishDiagnostics params)


(* Notifications *)

let update_metadata server metadata =
  let update = 
    function
    | Metadata.TypeAt (span, pp_env, tp) ->
      let info = Format.asprintf "%a" (Syntax.pp_tp pp_env) tp in
      server.hover_info <- IntervalTree.insert (Pos.of_lex_span span) info server.hover_info
    | Metadata.HoleAt (span, _, hole) ->
      server.holes <- IntervalTree.insert (Pos.of_lex_span span) hole server.holes
  in List.iter update metadata

let load_file server (uri : DocumentUri.t) =
  let path = DocumentUri.to_path uri in
  let* _ = LspLwt.log server.lsp_io "Loading File: %s" path in
  let* (diagnostics, metadata) = Executor.elaborate_file server.library path in
  let+ _ = publish_diagnostics server path diagnostics in
  update_metadata server metadata

let handle_notification : server -> string -> notification -> unit Lwt.t =
  fun server mthd ->
  function
  | TextDocumentDidOpen doc ->
    load_file server doc.textDocument.uri
  | DidSaveTextDocument doc ->
    load_file server doc.textDocument.uri
  | _ ->
    raise (LspError (UnknownNotification mthd))

(* Code Actions/Commands *)
let supported_commands = ["cooltt.visualize"]

(* Requests *)

let hover server (opts : HoverParams.t) =
  IntervalTree.lookup (Pos.of_lsp_pos opts.position) server.hover_info |> Option.map @@ fun info ->
  Hover.create ~contents:(`MarkedString { value = info; language = None }) ()

let codeAction server (opts : CodeActionParams.t) =
  let holes = IntervalTree.containing (Pos.of_lsp_range opts.range) server.holes in
  let actions =
    holes |> List.filter_map @@ fun (Metadata.Hole {ctx; tp}) ->
    Actions.Visualize.create ctx tp
    |> Option.map @@ fun action -> `CodeAction action

  in
  Lwt.return @@ Some actions

let executeCommand server (opts : ExecuteCommandParams.t) =
  let* _ = Actions.Visualize.execute opts.arguments in
  let ppargs = Format.asprintf "%a" (Format.pp_print_option (Format.pp_print_list Json.pp)) opts.arguments in
  let+ _ = LspLwt.log server.lsp_io "Execute Command: %s %s" opts.command ppargs in
  `Null

let handle_request : type resp. server -> string -> resp request -> resp Lwt.t =
  fun server mthd ->
  function
  | Initialize _ ->
    raise (LspError (HandshakeError "Server can only recieve a single initialization request."))
  | Shutdown ->
    Lwt.return ()
  | TextDocumentHover opts ->
    Lwt.return @@ hover server opts
  | CodeAction opts -> codeAction server opts
  | ExecuteCommand opts -> executeCommand server opts
  | _ -> raise (LspError (UnknownRequest mthd))

(* Main Event Loop *)
let on_notification server (notif : rpc_notification) =
  let* _ = LspLwt.log server.lsp_io "Notification: %s" notif.method_ in
  match Notification.of_jsonrpc notif with
  | Ok n -> handle_notification server notif.method_ n
  | Error err ->
    raise (LspError (DecodeError err))

let on_request server (req : rpc_request) =
  let* _ = LspLwt.log server.lsp_io "Request: %s" req.method_ in
  match Request.of_jsonrpc req with
  | Ok (E r) ->
    let+ resp = handle_request server req.method_ r in
    let json = Request.yojson_of_result r resp in
    RPC.Response.ok req.id json
  | Error err ->
    raise (LspError (DecodeError err))

let on_message server (msg : rpc_message) =
  match msg.id with
  | None -> on_notification server { msg with id = () }
  | Some id ->
    let* resp = on_request server { msg with id } in
    LspLwt.send server.lsp_io (RPC.Response resp)

(** Attempt to recieve a request from the client. *)
let recv_request lsp_io =
  let+ msg = LspLwt.recv lsp_io in
  Option.bind msg @@
  function
  | (Jsonrpc.Message ({ id = Some id; _ } as msg)) -> Some { msg with id }
  | _ -> None

(** Attempt to recieve a notification from the client. *)
let recv_notification lsp_io =
  let+ msg = LspLwt.recv lsp_io in
  Option.bind msg @@
  function
  | (Jsonrpc.Message ({ id = None; _ } as msg)) -> Some { msg with id = () }
  | _ -> None

(* Initialization *)

let server_capabilities =
  let textDocumentSync =
    let opts = TextDocumentSyncOptions.create
        ~change:(TextDocumentSyncKind.None)
        ~save:(`SaveOptions (SaveOptions.create ~includeText:false ()))
        ()
    in
    `TextDocumentSyncOptions opts
  in
  let hoverProvider =
    let opts = HoverOptions.create ()
    in `HoverOptions opts
  in
  let codeActionProvider =
    let opts = CodeActionOptions.create ~codeActionKinds:[CodeActionKind.Other "cooltt.hole.visualize"] () in
    `CodeActionOptions opts
  in
  let executeCommandProvider =
    ExecuteCommandOptions.create ~commands:supported_commands ()
  in
  ServerCapabilities.create
    ~textDocumentSync
    ~hoverProvider
    ~codeActionProvider
    ~executeCommandProvider
    ()

let library_manager =
  match Bantorra.Manager.init ~anchor:"cooltt-lib" ~routers:[] with
  | Ok ans -> ans
  | Error (`InvalidRouter err) -> raise (LspError (HandshakeError err)) (* this should not happen! *)

let initialize_library root =
  match
    match root with
    | Some path -> Bantorra.Manager.load_library_from_dir library_manager path
    | None -> Bantorra.Manager.load_library_from_cwd library_manager
  with
  | Ok (lib, _) -> lib
  | Error (`InvalidLibrary err) -> raise (LspError (HandshakeError err))

let get_root (init_params : InitializeParams.t) : string option =
  match init_params.rootUri with
  | Some uri -> Some (DocumentUri.to_path uri)
  | None -> Option.join init_params.rootPath

(** Perform the LSP initialization handshake.
    https://microsoft.github.io/language-server-protocol/specifications/specification-current/#initialize *)
let initialize lsp_io =
  let* req = recv_request lsp_io in
  match req with
  | Some req ->
    begin
      match Request.of_jsonrpc req with
      | Ok (E (Initialize init_params as init_req)) ->
        let* _ = LspLwt.log lsp_io "Initializing..." in
        let resp = InitializeResult.create ~capabilities:server_capabilities () in
        let json = Request.yojson_of_result init_req resp in
        let* _ = LspLwt.send lsp_io (RPC.Response (RPC.Response.ok req.id json)) in
        let* notif = recv_notification lsp_io in
        begin
          match notif with
          | Some notif ->
            begin
              match Notification.of_jsonrpc notif with
              | Ok Initialized ->
                let root = get_root init_params in
                let+ _ = LspLwt.log lsp_io "Root: %s" (Option.value root ~default:"<no-root>") in
                { lsp_io;
                  should_shutdown = false;
                  library = initialize_library root;
                  hover_info = IntervalTree.empty;
                  holes = IntervalTree.empty
                }
              | _ ->
                raise (LspError (HandshakeError "Initialization must complete with an initialized notification."))
            end
          | None ->
            raise (LspError (HandshakeError "Initialization must complete with an initialized notification."))
        end
      | Ok (E _) ->
        raise (LspError (HandshakeError "Initialization must begin with an initialize request."))
      | Error err ->
        raise (LspError (HandshakeError err))
    end
  | None ->
    raise (LspError (HandshakeError "Initialization must begin with a request."))

(* Shutdown *)

(** Perform the LSP shutdown sequence.
    See https://microsoft.github.io/language-server-protocol/specifications/specification-current/#exit *)
let shutdown server =
  let* notif = recv_notification server.lsp_io in
  match notif with
  | Some notif ->
    begin
      match Notification.of_jsonrpc notif with
      | Ok Exit ->
        Lwt.return ()
      | Ok _ ->
        raise (LspError (ShutdownError "The only notification that can be recieved after a shutdown request is exit."))
      | Error err -> 
        raise (LspError (ShutdownError err))
    end
  | None ->
    raise (LspError (ShutdownError "No requests can be recieved after a shutdown request."))

let print_exn lsp_io exn =
  let msg = Printexc.to_string exn
  and stack = Printexc.get_backtrace () in
  LspLwt.log lsp_io "%s\n%s" msg stack

let rec event_loop server =
  let* msg = LspLwt.recv server.lsp_io in
  match msg with
  | Some (Jsonrpc.Message msg) ->
    let* _ = Lwt.catch
        (fun () -> on_message server msg)
        (print_exn server.lsp_io)
    in
    if server.should_shutdown
    then
      shutdown server
    else 
      event_loop server
  | _ ->
    let+ _ = LspLwt.log server.lsp_io "Recieved an invalid message. Shutting down..." in
    ()


let run () =
  let () = Printexc.record_backtrace true in
  let lsp_io = LspLwt.init () in
  let action =
    let* server = initialize lsp_io in
    event_loop server
  in
  let _ = Lwt_main.run @@ Lwt.catch (fun () -> action) (print_exn lsp_io) in
  Ok ()
