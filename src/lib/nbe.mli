module Syn :
sig
  type uni_level = int
  type t =
    | Var of int (* DeBruijn indices for variables *)
    | Nat | Zero | Suc of t | NRec of t * t * t * t
    | Pi of t * t | Lam of t | Ap of t * t
    | Sig of t * t | Pair of t * t | Fst of t | Snd of t
    | Uni of uni_level

  type env = t list
end

exception Nbe_failed of string

val normalize : env:Syn.env -> term:Syn.t -> tp:Syn.t -> Syn.t
