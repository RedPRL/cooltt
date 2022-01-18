open Yuujinchou

type 'a t = 'a Trie.t

let empty = Trie.empty
let add ident sym ns =
  match ident with
  | `User path -> Trie.update_singleton path (fun _ -> Some sym) ns
  | _ -> ns

exception CRLF (* Can Reed Love Forever *)

(* XXX No [failwith]! *)
let nest pp_a modifier imported ns =
  let report_duplicate ~rev_path _old _new =
    failwith @@ "Duplicate identifiers for " ^ Ident.to_string (`User (List.rev rev_path))
  in
  let hooks cmd ~rev_prefix t =
    match cmd with
    | `Print lbl ->
      let lbl = Option.fold ~none:"?" ~some:(fun lbl -> "?" ^ lbl) lbl in
      Format.printf "@[<v2>Emitted namespace under %a:@,%s = @[{ "
        Ident.pp (`User (List.rev rev_prefix)) lbl;
      let first = ref true in (* XXX NON-functional programming! *)
      Trie.iteri (fun ~rev_path sym ->
          if not !first then Format.printf "@,; ";
          first := false; (* XXX there are 100 ways to avoid references *)
          Format.printf "@[<hov>%a =>@ %a@]" Ident.pp (`User (List.rev rev_path)) pp_a sym) t;
      Format.printf "@ }@]@]@.@.";
      Result.ok t
    | `ExpandRoot ->
      begin
        match Trie.find_root t with
        | Some _ -> raise CRLF
        | None -> Error (`BindingNotFound (List.rev rev_prefix))
      end
  in
  match Action.run_with_hooks ~hooks ~union:report_duplicate modifier imported with
  | Ok transformed_imported ->
    Trie.union report_duplicate ns transformed_imported
  | Error (`BindingNotFound path) ->
    failwith @@ "No identifiers with the prefix " ^ Ident.to_string (`User path)

let find (ident : Ident.t) ns =
  match ident with
  | `User path -> Trie.find_singleton path ns
  | _ -> None
