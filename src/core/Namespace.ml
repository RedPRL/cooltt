open Bwd
open Yuujinchou

type path = Yuujinchou.Trie.path

module Param = struct
  type data = CodeUnit.Global.t
  type tag = unit
  type hook = [`Print of string option]
  type context = |
end
module M = Modifier.Make(Param)

type t = CodeUnit.Global.t Trie.Untagged.t
type pattern = [`Print of string option ] Yuujinchou.Language.t

exception BindingNotFound of path
exception Shadowing of path
type ('a, 'error) result = ('a, [> `BindingNotFound of path | `Shadowing of path ] as 'error) Stdlib.result

let empty = Trie.empty

let prefix = Trie.prefix

let merge ~shadowing path _ x =
  if shadowing then x else raise @@ Shadowing (Bwd.to_list path)

let transform ~shadowing ~pp pat ns =
  let not_found _ path = raise @@ BindingNotFound (Bwd.to_list path) in
  let hook _ path (`Print lbl) t =
    let lbl = Option.fold ~none:"?" ~some:(fun lbl -> "?" ^ lbl) lbl in
    Format.printf "@[<v2>Emitted namespace under %a@,%s = @[{ "
      Ident.pp (`User (Bwd.to_list path)) lbl;
    let first = ref true in (* XXX NON-functional programming! *)
    Trie.Untagged.iter (fun path sym ->
        if not !first then Format.printf "@,; ";
        first := false; (* XXX there are 100 ways to avoid references *)
        Format.printf "@[<hov>%a =>@ %a@]" Ident.pp (`User (Bwd.to_list path)) pp sym) t;
    Format.printf "@ }@]@]@.@.";
    t
  in
  try Result.ok @@ M.run ~not_found ~shadow:(fun _ctx -> merge ~shadowing) ~hook @@ fun () -> M.modify pat ns with
  | BindingNotFound p -> Result.error @@ `BindingNotFound p
  | Shadowing p -> Result.error @@ `Shadowing p

let union ~shadowing ns1 ns2 =
  try Result.ok @@ Trie.Untagged.union (merge ~shadowing) ns1 ns2 with
  | Shadowing p -> Result.error @@ `Shadowing p

let merge1 ~shadowing path x old_x =
  if Option.is_none old_x || shadowing
  then Some x
  else raise @@ Shadowing (Bwd.to_list path)

let add ~shadowing ident sym ns =
  match ident with
  | `User path ->
    begin
      try Result.ok @@ Trie.Untagged.update_singleton path (merge1 ~shadowing (Bwd.of_list path) sym) ns with
      | Shadowing p -> Result.error @@ `Shadowing p
    end
  | _ -> Result.ok ns

let find (ident : Ident.t) ns =
  match ident with
  | `User path -> Trie.Untagged.find_singleton path ns
  | _ -> None
