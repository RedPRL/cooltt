open Basis

val elaborate_file : Bantorra.Manager.library -> string -> Lsp.Types.Diagnostic.t list Lwt.t
