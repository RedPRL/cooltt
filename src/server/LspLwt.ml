(** LSP Server IO, implemented using LWT. *)
module LwtIO = Lwt_io
open Lsp.Import

type io = { ic : LwtIO.input_channel;
            oc : LwtIO.output_channel;
            logc : LwtIO.output_channel
          }

let init () =
  { ic = LwtIO.stdin; oc = LwtIO.stdout; logc = LwtIO.stderr }

module Notation = struct
  let (let*) = Lwt.bind
  let (let+) m f = Lwt.map f m 
  let (and*) = Lwt.both
end

open Notation

(* Logging *)

(** Log out a message to stderr. *)
let log (io : io) (msg : string) : unit Lwt.t =
  LwtIO.fprintl io.logc msg

(** See https://microsoft.github.io/language-server-protocol/specifications/specification-current/#headerPart *)
module Header = struct
  type t = { content_length : int;
             content_type : string
           }

  let empty = { content_length = -1;
                content_type = "application/vscode-jsonrpc; charset=utf-8"
              }

  let create ~(content_length : int) : t =
    { empty with content_length }

  let is_content_length key =
    String.equal (String.lowercase_ascii @@ String.trim key) "content-length" 

  let is_content_type key =
    String.equal (String.lowercase_ascii @@ String.trim key) "content-type" 

  (* NOTE: We should never really recieve an invalid header, as
     that would indicate a broken client implementation. Therefore,
     we just bail out when we see an invalid header, as there's 
     way we can really recover anyways. *)
  type header_error =
    | InvalidHeader of string
    | InvalidContentLength of string

  exception HeaderError of header_error

  let () = Printexc.register_printer @@
    function
    | HeaderError (InvalidHeader err) -> Some (Format.asprintf "HeaderError: Invalid Header %s" err)
    | HeaderError (InvalidContentLength n) -> Some (Format.asprintf "HeaderError: Invalid Content Length '%s'" n)
    | _ -> None

  (** Read the header section of an LSP message. *)
  let read (io : io) : t Lwt.t =
    let rec loop headers =
      Lwt.bind (LwtIO.read_line io.ic) @@
      function
      | "" -> Lwt.return headers
      | line ->
        match String.split_on_char ~sep:':' @@ String.trim line with
        | [key; value] when is_content_length key ->
          let content_length =
            match int_of_string_opt (String.trim value) with
            | Some n -> n
            | None -> raise (HeaderError (InvalidContentLength value))
          in loop { headers with content_length }
        | [key; value] when is_content_type key ->
          let content_type = String.trim value in
          loop { headers with content_type }
        | [_; _] -> loop headers
        | _ ->
          raise (HeaderError (InvalidHeader line))
    in
    loop empty |> Lwt.map @@ fun headers ->
    if headers.content_length < 0 then
      raise (HeaderError (InvalidContentLength (string_of_int headers.content_length)))
    else
      headers

  let write (io : io) (headers : t) : unit Lwt.t =
    LwtIO.fprintf io.oc "Content-Type: %s\r\nContent-Length: %d\r\n\r\n" headers.content_type headers.content_length
end

let read_content (io : io) : string option Lwt.t =
  let action =
    let* header = Header.read io in
    let len = header.content_length in
    let buffer = Bytes.create len in
    let rec loop bytes_read =
      if bytes_read < len then
        let* n = LwtIO.read_into io.ic buffer bytes_read (len - bytes_read) in
        loop (bytes_read + n)
      else
        Lwt.return @@ Some (Bytes.to_string buffer)
    in loop 0
  in
  Lwt.catch (fun () -> action) @@
  function
  | Sys_error _ -> Lwt.return None
  | End_of_file -> Lwt.return None
  | exn -> Lwt.fail exn

let read_json (io : io) : Json.t option Lwt.t =
  let+ contents = read_content io in
  Option.map Json.of_string contents

let recv (io : io) : Jsonrpc.packet option Lwt.t =
  let+ json = read_json io in
  json |> Option.map @@ fun json ->
  let open Json.O in
  let req json = Jsonrpc.Message (Jsonrpc.Message.either_of_yojson json) in
  let resp json = Jsonrpc.Response (Jsonrpc.Response.t_of_yojson json) in
  (req <|> resp) json

let send (io : io) (packet : Jsonrpc.packet) : unit Lwt.t =
  let json = Jsonrpc.yojson_of_packet packet in
  let data = Json.to_string json in
  let content_length = String.length data in
  let header = Header.create ~content_length in
  let* _ = Header.write io header in
  let* _ = LwtIO.write io.oc data in
  LwtIO.flush io.oc

