open Yuujinchou

type 'a t = 'a Trie.t

let empty = Trie.empty
let add ident sym ns =
  match ident with
  | `User path -> Trie.update_singleton path (fun _ -> Some sym) ns
  | _ -> ns

let nest parts imported ns =
  let report_duplicate ~rev_path _old _new =
    failwith @@ "Duplicate identifiers for " ^ Ident.to_string (`User (List.rev rev_path))
  in
  Trie.union_subtree report_duplicate ns (parts, imported)

let find (ident : Ident.t) ns =
  match ident with
  | `User path -> Trie.find_singleton path ns
  | _ -> None
