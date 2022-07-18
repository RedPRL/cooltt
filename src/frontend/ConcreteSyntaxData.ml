open Basis
open Core

(* [HACK: June; 2022-07-14] We are using Yojson to avoid having to write a serializer
   for concrete syntax by hand. However, the rest of cooltt uses Ezjsonm. In my mind, this
   is justification to dump Ezjsonm. But for now, we need a converter.

   Maybe this should go somewhere else. But considering that this is /the/ module that uses
   Yojson, I put it here. *)

module J = Ezjsonm
module Y = Yojson.Safe

let rec yojson_of_ezjsonm (j : J.value) : Y.t =
  match j with
  | `A vals -> `List (List.map yojson_of_ezjsonm vals)
  | `O vals -> `Assoc (List.map (fun (k, v) -> (k, yojson_of_ezjsonm v)) vals)
  (* [HACK: June; 2022-07-14] Do we need more sophisticated float conversion? *)
  | `Float f -> `Float f
  | `Null -> `Null
  | `Bool b -> `Bool b
  | `String s -> `String s

let rec ezjsonm_of_yojson (j : Y.t) : J.value =
  match j with
  | `List vals
  | `Tuple vals -> `A (List.map ezjsonm_of_yojson vals)
  | `Assoc vals -> `O (List.map (fun (k, v) -> (k, ezjsonm_of_yojson v)) vals)
  | `Variant (label, Some x) -> `A [`String label; ezjsonm_of_yojson x]
  | `Variant (label, None) -> `String label
  | `Intlit i -> `String i
  | `Null -> `Null
  | `Float f -> `Float f
  | `Bool b -> `Bool b
  | `String s -> `String s
  | `Int i -> `Float (float_of_int i)

type info = LexingUtil.span option

let pp_info fmt =
  function
  | None -> Format.fprintf fmt "Unknown location"
  | Some span ->
    LexingUtil.pp_span fmt span

type 'a node =
  {node : 'a;
   info : (info [@yojson.opaque])
  }
[@@deriving show, yojson]

type hole = {name: string option; silent: bool}
[@@deriving show, yojson]

let map_node ~f n = {n with node = f n.node}
let get_info n = n.info

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
  | Patch of con * patch_field list
  | Open of con * (Ident.user * Ident.user) list * con
  | Sub of con * con * con
  | Pair of con * con
  | Fst of con
  | Snd of con
  | Type
  | Hole of hole * con option
  | BoundaryHole of con option
  | Visualize
  | Edit
  | Underscore
  | Generalize of Ident.t * con
  | Unfold of Ident.t list * con
  | Abstract of Ident.t option * con
  | Elim of {mot : con; cases : case list; scrut : con}
  | Rec of {mot : con; cases : case list; scrut : con}
  | LamElim of case list
  | Equations of { code : con; eqns : eqns step }
  | Dim
  | Cof
  | CofEq of con * con
  | CofLe of con * con
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
  | HComChk of con * con * con
  | HFill of con * con * con * con
  | HFillChk of con * con
  | Com of con * con * con * con * con
  | V of con * con * con * con
  | VProj of con
  | Cap of con
  | ModAny
  | ModOnly of string list
  | ModRename of string list * string list
  | ModNone
  | ModExcept of string list
  | ModSeq of con list
  | ModUnion of con list
  | ModInSubtree of string list * con
  | ModPrint of hole
[@@deriving show, yojson]

and case = pat * con
[@@deriving show]

and field = [`Field of Ident.user * con | `Include of con * (Ident.user * Ident.user) list]
[@@deriving show]

and patch_field = [`Patch of Ident.user * con | `Subst of Ident.user * con]
[@@deriving show]

and pat = Pat of {lbl : string list; args : pat_arg list}
[@@deriving show]

and pat_arg = [`Simple of Ident.t | `Inductive of Ident.t * Ident.t]
[@@deriving show]

and 'a step =
  | Equals of con * con * 'a
  | Trivial of con * 'a

and eqns =
  | Step of eqns step
  | Qed of con

type decl = decl_ node
and decl_ =
  | Def of {abstract : bool; shadowing : bool; name : Ident.t; args : cell list; def : con; tp : con; unfolding : Ident.t list}
  | Axiom of {shadowing : bool; name : Ident.t; args : cell list; tp : con}
  | Print of {unfolding : Ident.t list; name : Ident.t node}
  | Import of {shadowing : bool; unitpath : string list; modifier : con option}
  | NormalizeTerm of {unfolding : Ident.t list; con : con}
  | Fail of decl
  | Quit
  | View of {shadowing : bool; modifier : con}
  | Export of {shadowing : bool; modifier : con}
  | Repack of {shadowing : bool; modifier : con}
  | Section of {shadowing : bool; prefix : string list option; decls : signature; modifier : con option}
[@@deriving show]

and signature = decl list

type repl_command = repl_command_ node
and repl_command_ =
  | NoOp
  | EndOfFile
  | Decl of decl
