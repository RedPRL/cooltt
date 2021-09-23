open Basis
open Core

type info = LexingUtil.span option

let pp_info fmt =
  function
  | None -> Format.fprintf fmt "Unknown location"
  | Some span ->
    LexingUtil.pp_span fmt span


type 'a node =
  {node : 'a;
   info : info}

[@@deriving show]


type cell = Cell of {names : Ident.t list; tp : con}
and con = con_ node
and con_ =
  | Var of Ident.t
  | DeBruijnLevel of int
  | Let of con * Ident.t * con
  | Ann of {term : con; tp : con}
  | Nat
  | Suc of con
  | Lit of int
  | Circle
  | Base
  | Loop of con
  | Pi of cell list * con
  | Lam of Ident.t list * con
  | Ap of con * con list
  | Sg of cell list * con
  | Signature of field list
  | Struct of field list
  | Proj of con * Ident.user
  | Patch of con * field list
  | Total of con * field list
  | Sub of con * con * con
  | Pair of con * con
  | Fst of con
  | Snd of con
  | Type
  | Hole of string option * con option
  | BoundaryHole of con option
  | Underscore
  | Unfold of Ident.t list * con
  | Generalize of Ident.t * con
  | Elim of {mot : con; cases : case list; scrut : con}
  | Rec of {mot : con; cases : case list; scrut : con}
  | LamElim of case list
  | Dim
  | Cof
  | CofEq of con * con
  | Join of con list
  | Meet of con list
  | CofBoundary of con
  | Prf of con
  | CofSplit of (con * con) list
  | Ext of Ident.t list * con * (con * con) list
  | Coe of con * con * con * con
  | TopC
  | BotC
  | HCom of con * con * con * con * con
  | HFill of con * con * con * con
  | Com of con * con * con * con * con
  | V of con * con * con * con
  | VProj of con
  | Cap of con
  | Locked of con
  | Unlock of con * con
  | ModAny
  | ModOnly of string list
  | ModRename of string list * string list
  | ModNone
  | ModExcept of string list
  | ModSeq of con list
  | ModUnion of con list
  | ModInSubtree of string list * con
  | ModPrint of string option
[@@deriving show]

and case = pat * con
[@@deriving show]

and field = Field of { lbl : Ident.user; tp : con }
[@@deriving show]

and pat = Pat of {lbl : string list; args : pat_arg list}
[@@deriving show]

and pat_arg = [`Simple of Ident.t | `Inductive of Ident.t * Ident.t]
[@@deriving show]

type decl =
  | Def of {name : Ident.t; args : cell list; def : con option; tp : con}
  | Data of { name : Ident.t; params : con; ctors: field list }
  | Print of Ident.t node
  | Import of string list * con option
  | NormalizeTerm of con
  | Fail of {name : Ident.t; args : cell list; def : con; tp : con; info : info}
  | Quit

type command =
  | NoOp
  | EndOfFile
  | Decl of decl

type signature = decl list
