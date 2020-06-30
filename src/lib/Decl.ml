open Basis
open Cubical

module S = Syntax

type t =
  | Hidden of S.tp
  | Return of S.tp * S.t
  | Abs of S.tp * Ident.t * t
           (*
  | ByNatElim of {mot : S.t; zero : S.t; suc : S.t}
              *)

let ppenv_bind env ident =
  Pp.Env.bind env @@
  match ident with
  | `Anon -> None
  | `User id -> Some id
  | `Machine id -> Some id

let pp_sequent_goal env fmt tp  =
  match tp with
  | S.GoalTp (_, Sub (tp, Cof (Cof.Join []), _)) ->
    Format.fprintf fmt "@[<hov>%a@]"
      (S.pp_tp env) tp
  | S.GoalTp (_, Sub (tp, phi, tm)) ->
    let _x, envx = Pp.Env.bind env (Some "_") in
    Format.fprintf fmt "@[<hv>%a@ [%a => %a]"
      (S.pp_tp env) tp
      (S.pp env) phi
      (S.pp envx) tm
  | S.GoalTp (_, tp) ->
    Format.fprintf fmt "@[<hov>%a@]"
      (S.pp_tp env) tp
  | tp ->
    S.pp_tp env fmt tp


let rec pp_decl_inner env ident fmt =
  function
  | Abs (base, ident', decl) ->
    let x, envx = ppenv_bind env ident' in
    Format.fprintf fmt "%a : %a@;%a"
      Uuseg_string.pp_utf_8 x
      (S.pp_tp env) base
      (pp_decl_inner envx ident) decl
  | Hidden tp ->
    Format.fprintf fmt "@[<v>%a %a@ : %a@]"
      Uuseg_string.pp_utf_8 "⊢"
      Ident.pp ident
      (pp_sequent_goal env) tp
  | Return (tp, tm) ->
    Format.fprintf fmt "@[<v>%a %a@ = @[<hov>%a@]@ : @[<hov>%a@]@]"
      Uuseg_string.pp_utf_8 "⊢"
      Ident.pp ident
      (S.pp env) tm
      (pp_sequent_goal env) tp

(*
  | ByNatElim _ ->
    Format.fprintf fmt "<nat-elim>"
   *)


let pp ident fmt decl =
  Format.fprintf fmt "@[<v>%a@]"
    (pp_decl_inner Pp.Env.emp ident) decl
