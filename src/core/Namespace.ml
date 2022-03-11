open Yuujinchou

type path = Pattern.path

type 'a t = 'a Trie.t
type 'a pattern = ([< `Print of string option] as 'a) Pattern.t
type ('a, 'error) result = ('a, [> `BindingNotFound of path | `Shadowing of path ] as 'error) Stdlib.result

let empty = Trie.empty

let merge ~shadowing ~rev_path _ x =
  if shadowing
  then Result.ok x
  else Result.error (`Shadowing (List.rev rev_path))

let transform ~shadowing ~pp pat ns =
  let hooks (`Print lbl) ~rev_prefix t =
    let lbl = Option.fold ~none:"?" ~some:(fun lbl -> "?" ^ lbl) lbl in
    Format.printf "@[<v2>Emitted namespace under %a:@,%s = @[{ "
      Ident.pp (`User (List.rev rev_prefix)) lbl;
    let first = ref true in (* XXX NON-functional programming! *)
    Trie.iteri (fun ~rev_path sym ->
        if not !first then Format.printf "@,; ";
        first := false; (* XXX there are 100 ways to avoid references *)
        Format.printf "@[<hov>%a =>@ %a@]" Ident.pp (`User (List.rev rev_path)) pp sym) t;
    Format.printf "@ }@]@]@.@.";
    Result.ok t
  in
  Action.run_with_hooks ~hooks ~union:(merge ~shadowing) pat ns

let union ~shadowing ns1 ns2 =
  Trie.Result.union (merge ~shadowing) ns1 ns2

let merge1 ~shadowing ~path x old_x =
  if Option.is_none old_x || shadowing
  then Result.ok (Some x)
  else Result.error (`Shadowing (List.rev path))

let add ~shadowing ident sym ns =
  match ident with
  | `User path ->
    Trie.Result.update_singleton path (merge1 ~shadowing ~path sym) ns
  | _ ->
    Result.ok ns

let find (ident : Ident.t) ns =
  match ident with
  | `User path -> Trie.find_singleton path ns
  | _ -> None
