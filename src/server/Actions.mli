open Basis
open Core
open CodeUnit

module Json = Lsp.Import.Json

module Visualize : sig
  val command_name : string
  val create : (Ident.t * Syntax.tp) list -> Syntax.tp -> Lsp.Types.CodeAction.t option
  val execute : Json.t list option -> unit Lwt.t
end
