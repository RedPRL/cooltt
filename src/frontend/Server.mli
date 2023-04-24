open Core
open CodeUnit

module CS := ConcreteSyntax
module D := Domain
module T := Tactic
module S := Syntax
module RM := RefineMonad

val init : string -> int -> unit
val close : unit -> unit

val dispatch_goal : (Ident.t * S.tp) list -> S.tp -> unit

val send_faces : (Ident.t * S.tp) list -> (D.tp * D.cof * D.tm_clo) list -> CS.con option RM.m
