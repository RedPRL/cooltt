open Basis
open Core

val elaborate_file : Bantorra.Manager.library -> string -> (Lsp.Types.Diagnostic.t list * RefineState.Metadata.t) Lwt.t
