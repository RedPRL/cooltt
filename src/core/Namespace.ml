open Yuujinchou

type 'a t = 'a Trie.t

let empty = Trie.empty
let add ident sym ns =
  match ident with
  | `User path -> Trie.update_singleton path (fun _ -> Some sym) ns
  | _ -> ns

(* XXX No [failwith]! *)
let nest modifier imported ns =
  let report_duplicate ~rev_path _old _new =
    failwith @@ "Duplicate identifiers for " ^ Ident.to_string (`User (List.rev rev_path))
  in
  match Action.run ~union:report_duplicate modifier imported with
  | Ok transformed_imported ->
    Trie.union report_duplicate ns transformed_imported
  | Error (`BindingNotFound path) ->
    failwith @@ "No identifier at " ^ Ident.to_string (`User path)

let find (ident : Ident.t) ns =
  match ident with
  | `User path -> Trie.find_singleton path ns
  | _ -> None
