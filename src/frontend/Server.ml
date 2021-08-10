open Core
open CodeUnit

module S = Syntax

module J = Ezjsonm

(* [NOTE: Cooltt Server]
   We use a 'ref' here to prevent having to thread down a server handle
   deep into the guts of the elaborator. *)
let server : Unix.file_descr option ref =
  ref None

let init port =
  try
    Format.eprintf "Initializing cooltt server connection on port %n...@." port;
    let socket = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    let localhost = Unix.inet_addr_of_string "127.0.0.1" in
    let () = Unix.connect socket (Unix.ADDR_INET (localhost, port)) in
    Format.eprintf "Cooltt server connection initialized@.";
    server := Some socket
  with Unix.Unix_error _ ->
    Format.eprintf "Error: Could not initialize cooltt server connection.@."

let close () =
  match !server with
  | Some socket ->
    Unix.close socket;
    server := None
  | None -> ()

let dispatch_goal ctx goal =
  match !server with
  | Some socket ->
    begin
      try
        (* FIXME: Be smarter about the buffer sizes here. *)
        let buf = Buffer.create 65536 in
        J.to_buffer ~minify:true buf @@ Serialize.serialize_goal ctx goal;
        let nbytes = Unix.send socket (Buffer.to_bytes buf) 0 (Buffer.length buf) [] in
        Debug.print "Sent %n bytes to Server.@." nbytes;
        ()
      with Unix.Unix_error _ ->
        Format.eprintf "Cooltt server connection lost.@.";
        close ()
    end
  | None -> ()
