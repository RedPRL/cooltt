module StringMap = Map.Make (String)

type 'a t = {
    (** Used to resolve an identifier to a unique symbol in this namespace. *)
    names : 'a StringMap.t;
    (** Namespaces may themselves contain other namespaces, so let's keep track of them. *)
    namespaces : ('a t) StringMap.t
  }

let empty = { names = StringMap.empty; namespaces = StringMap.empty }

(* Adding Symbols/Namespaces *)

let update_namespace str f ns =
  { ns with namespaces = StringMap.update str (fun opt -> Some (f @@ Option.value opt ~default:empty)) ns.namespaces }

let rec add_qualified_symbol parts nm sym ns =
  match parts with
  | [] -> { ns with names = StringMap.add nm sym ns.names }
  | (part :: parts) -> update_namespace part (add_qualified_symbol parts nm sym) ns

let add (ident : Ident.t) sym ns =
  match ident with
  | `User (parts, nm) -> add_qualified_symbol parts nm sym ns
  | _           -> ns

(* FIXME: Deal with naming conflicts better! *)
let rec merge_namespaces ns ns' =
  { names = StringMap.union (fun nm _ _-> failwith @@ "Duplicate identifiers for " ^ nm) ns.names ns'.names;
    namespaces = StringMap.union (fun _ nested nested' -> Some (merge_namespaces nested nested')) ns.namespaces ns'.namespaces }

let rec nest parts imported ns =
  match parts with
  | [] -> merge_namespaces imported ns
  | (part :: parts) -> update_namespace part (nest parts imported) ns


(* Name Resolution *)

let rec resolve_qualified modparts nm ns =
  match modparts with
  | [] -> StringMap.find_opt nm ns.names
  | (modnm :: modparts) -> Option.bind (StringMap.find_opt modnm ns.namespaces) (resolve_qualified modparts nm)

let find (ident : Ident.t) ns =
  match ident with
  | `User (parts, nm) -> resolve_qualified parts nm ns
  | _                 -> None
