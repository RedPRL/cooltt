open Basis

module S = Syntax

type t =
  | Hidden of S.tp
  | Return of S.tp * S.t
  | Abs of S.tp * Ident.t * t

let rec tp_of_decl =
  function
  | Return (tp, _) | Hidden tp ->
    tp
  | Abs (base, ident, decl) ->
    S.Pi (base, ident, tp_of_decl decl)

let ppenv_bind env ident =
  Pp.Env.bind env @@
  match ident with
  | `Anon -> None
  | `User id -> Some id
  | `Machine id -> Some id

let rec pp_decl_bdy env fmt =
  function
  | Hidden tp ->
    Format.fprintf fmt ": %a"
      (S.pp_tp env) tp
  | Return (tp, tm) ->
    Format.fprintf fmt ": %a =@ %a"
      (S.pp_tp env) tp
      (S.pp env) tm
  | Abs (base, ident, decl) ->
    let x, envx = ppenv_bind env ident in
    Format.fprintf fmt "(%a : %a) %a"
      Uuseg_string.pp_utf_8 x
      (S.pp_tp env) base
      (pp_decl_bdy envx) decl


let pp ident fmt decl =
  Format.fprintf fmt "%a %a"
    Ident.pp ident
    (pp_decl_bdy Pp.Env.emp) decl
