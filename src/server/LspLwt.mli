type io

val init : unit -> io

module Notation : sig
  val (let*) : 'a Lwt.t -> ('a -> 'b Lwt.t) -> 'b Lwt.t
  val (let+) : 'a Lwt.t -> ('a -> 'b) -> 'b Lwt.t
  val (and*) : 'a Lwt.t -> 'b Lwt.t -> ('a * 'b) Lwt.t
end

val recv : io -> Jsonrpc.packet option Lwt.t
val send : io -> Jsonrpc.packet -> unit Lwt.t
val log  : io -> ('a, unit, string, unit Lwt.t) format4 -> 'a
