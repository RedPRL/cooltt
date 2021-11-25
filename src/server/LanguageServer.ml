open Basis
open Frontend
open Core
open CodeUnit

open Lsp.Types

module RPC = Jsonrpc
module Request = Lsp.Client_request
module Notification = Lsp.Client_notification
module Broadcast = Lsp.Server_notification

type rpc_message = RPC.Id.t option RPC.Message.t
type rpc_request = RPC.Message.request
type rpc_notification = RPC.Message.notification

type 'resp request = 'resp Lsp.Client_request.t
type notification = Lsp.Client_notification.t

type server =
  { lsp_io : LspLwt.io;
    mutable should_shutdown : bool
  }

type lsp_error =
  | DecodeError of string
  | HandshakeError of string
  | ShutdownError of string
  | UnknownRequest of string
  | UnknownNotification of string

exception LspError of lsp_error

open LspLwt.Notation

(* Notifications *)

(* Requests *)
let handle_notification : server -> string -> notification -> unit Lwt.t =
  fun server mthd ->
  function
  | _ -> raise (LspError (UnknownNotification mthd))

let handle_request : type resp. server -> string -> resp request -> resp Lwt.t =
  fun server mthd ->
  function
  | Initialize _ ->
    raise (LspError (HandshakeError "Server can only recieve a single initialization request."))
  | Shutdown ->
    Lwt.return ()
  | _ -> raise (LspError (UnknownRequest mthd))

(* Main Event Loop *)
let on_notification server (notif : rpc_notification) =
  match Notification.of_jsonrpc notif with
  | Ok n -> handle_notification server notif.method_ n
  | Error err ->
    raise (LspError (DecodeError err))

let on_request server (req : rpc_request) =
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
let recv_request server =
  let+ msg = LspLwt.recv server.lsp_io in
  Option.bind msg @@
  function
  | (Jsonrpc.Message ({ id = Some id; _ } as msg)) -> Some { msg with id }
  | _ -> None

(** Attempt to recieve a notification from the client. *)
let recv_notification server =
  let+ msg = LspLwt.recv server.lsp_io in
  Option.bind msg @@
  function
  | (Jsonrpc.Message ({ id = None; _ } as msg)) -> Some { msg with id = () }
  | _ -> None

(* Initialization *)

let server_capabilities =
  ServerCapabilities.create ()

(** Perform the LSP initialization handshake.
    https://microsoft.github.io/language-server-protocol/specifications/specification-current/#initialize *)
let initialize server =
  let* req = recv_request server in
  match req with
  | Some req ->
    begin
      match Request.of_jsonrpc req with
      | Ok (E (Initialize _ as init_req)) ->
        let* _ = LspLwt.log server.lsp_io "Initializing..." in
        let resp = InitializeResult.create ~capabilities:server_capabilities () in
        let json = Request.yojson_of_result init_req resp in
        LspLwt.send server.lsp_io (RPC.Response (RPC.Response.ok req.id json))
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
  let* notif = recv_notification server in
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

let rec event_loop server =
  let* msg = LspLwt.recv server.lsp_io in
  match msg with
  | Some (Jsonrpc.Message msg) ->
    let* _ = on_message server msg in
    if server.should_shutdown
    then
      shutdown server
    else 
      event_loop server
  | _ ->
    let+ _ = LspLwt.log server.lsp_io "Recieved an invalid message. Shutting down..." in
    ()

let run () =
  let server = {
    lsp_io = LspLwt.init ();
    should_shutdown = false
  } in
  let _ = Lwt_main.run @@
    let* _ = initialize server in
    event_loop server
  in Ok ()
