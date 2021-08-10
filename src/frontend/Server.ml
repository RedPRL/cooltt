open Core
open CodeUnit

module S = Syntax

module J = Ezjsonm

type t = Unix.file_descr

let init port =
  try
    Format.eprintf "Initializing cooltt server connection on port %n...@." port;
    let socket = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    let localhost = Unix.inet_addr_of_string "127.0.0.1" in
    let () = Unix.connect socket (Unix.ADDR_INET (localhost, port)) in
    Format.eprintf "Cooltt server connection initialized@.";
    socket
  with Unix.Unix_error (Unix.ECONNREFUSED,_,_) ->
    Format.eprintf "Error: Could not initialize cooltt server connection.@.";
    failwith "Cooltt server init failed."

let close socket =
  Unix.close socket

let dispatch_goal socket ctx goal =
  (* FIXME: Be smarter about the buffer sizes here. *)
  let buf = Buffer.create 65536 in
  J.to_buffer ~minify:true buf @@ Serialize.serialize_goal ctx goal;
  let nbytes = Unix.send socket (Buffer.to_bytes buf) 0 (Buffer.length buf) [] in
  Debug.print "Sent %n bytes to Server.@." nbytes;
  ()
