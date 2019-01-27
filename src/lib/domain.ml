type env = t list
[@@deriving show, eq]
and clos =
    Clos of {term : Syntax.t; env : env}
  | ConstClos of t
[@@deriving show, eq]
and clos2 = Clos2 of {term : Syntax.t; env : env}
[@@deriving show, eq]
and clos3 = Clos3 of {term : Syntax.t; env : env}
[@@deriving show, eq]
and t =
  | Lam of clos
  | Neutral of {tp : t; term : ne}
  | Nat
  | Zero
  | Suc of t
  | Pi of t * clos
  | Sig of t * clos
  | Pair of t * t
  | Box of t
  | Shut of t
  | Refl of t
  | Id of t * t * t
  | Uni of Syntax.uni_level
[@@deriving show, eq]
and ne =
  | Var of int (* DeBruijn levels for variables *)
  | Ap of ne * nf
  | Fst of ne
  | Snd of ne
  | Open of ne
  | NRec of clos * t * clos2 * ne
  | J of clos3 * clos * t * t * t * ne
[@@deriving show, eq]
and nf =
  | Normal of {tp : t; term : t}
[@@deriving show, eq]

let mk_var tp lev = Neutral {tp; term = Var lev}

let rec int_of_syn = function
  | Zero -> Some 0
  | Suc t ->
    begin
      match int_of_syn t with
      | Some i -> Some (i + 1)
      | None -> None
    end
  | _ -> None

(* let rec go_to_sexp size env = function *)
(*   | Nat -> Sexp.Atom "Nat" *)
(*   | Zero -> Sexp.Atom "zero" *)
(*   | Suc t -> *)
(*     begin *)
(*       match int_of_syn t with *)
(*       | Some i -> Sexp.Atom (string_of_int (i + 1)) *)
(*       | None -> Sexp.List [Sexp.Atom "suc"; go_to_sexp size env t] *)
(*     end *)
(*   | Pi (src, dest) -> *)
(*     Sexp.List *)
(*       [Sexp.Atom "Pi"; *)
(*        go_to_sexp size env src; *)
(*        go_to_sexp_clos size env dest] *)
(*   | Lam t -> *)
(*     Sexp.List [Sexp.Atom "lam"; go_to_sexp_clos size env t] *)
(*   | Sig (fst, snd) -> *)
(*     Sexp.List *)
(*       [Sexp.Atom "Sig"; *)
(*        go_to_sexp size env fst; *)
(*        go_to_sexp_clos size env snd] *)
(*   | Pair (t1, t2) -> *)
(*     Sexp.List [Sexp.Atom "pair"; go_to_sexp size env t1; go_to_sexp size env t2] *)
(*   | Uni i -> Sexp.List [Sexp.Atom "U"; Sexp.Atom (string_of_int i)] *)
(*   | Box t -> Sexp.List [Sexp.Atom "Box"; go_to_sexp size env t] *)
(*   | Shut t -> Sexp.List [Sexp.Atom "shut"; go_to_sexp size env t] *)
(*   | Neutral {tp; term} -> Sexp.List [Sexp.Atom "up"; go_to_sexp size env tp; go_to_sexp_ne size env term] *)

(* and go_to_sexp_clos size env = function *)
(*   | ConstClos t -> Sexp.List [Sexp.Atom "_"; go_to_sexp size env t] *)
(*   | Clos body -> *)
(*     let var = Sexp.Atom ("x" ^ string_of_int size) in *)
(*     let new_env = var :: List.map (go_to_sexp size env) body.env |> List.rev in *)
(*     Sexp.List [var; Syntax.to_sexp new_env body.term] *)

(* and go_to_sexp_ne size env = function *)
(*   | Var i -> *)
(*     if i >= size *)
(*     then Sexp.Atom ("x" ^ string_of_int i) *)
(*     else List.nth env i *)
(*   | Ap (f, a) -> *)
(*     Sexp.List [Sexp.Atom "ap"; go_to_sexp_ne size env f; go_to_sexp_nf size env a] *)
(*   | Fst p -> Sexp.List [Sexp.Atom "fst"; go_to_sexp_ne size env p] *)
(*   | Snd p -> Sexp.List [Sexp.Atom "snd"; go_to_sexp_ne size env p] *)
(*   | Open t -> Sexp.List [Sexp.Atom "open"; go_to_sexp_ne size env t] *)
(*   | NRec (motive, zero, Clos2 suc, n) -> *)
(*     let suc_var1 = Sexp.Atom ("x" ^ string_of_int (size + 1)) in *)
(*     let suc_var2 = Sexp.Atom ("x" ^ string_of_int (size + 2)) in *)
(*     let senv = suc_var2 :: suc_var1 :: List.map (go_to_sexp size env) suc.env |> List.rev in *)
(*     Sexp.List *)
(*       [Sexp.Atom "nrec"; *)
(*        go_to_sexp_clos size env motive; *)
(*        go_to_sexp size env zero; *)
(*        Sexp.List [suc_var1; suc_var2; Syntax.to_sexp senv suc.term]; *)
(*        go_to_sexp_ne size env n] *)

(* and go_to_sexp_nf size env (Normal {tp; term}) = *)
(*   Sexp.List *)
(*     [Sexp.Atom "down"; *)
(*      go_to_sexp size env tp; *)
(*      go_to_sexp size env term] *)

(* let to_sexp = go_to_sexp 0 [] *)
(* let to_sexp_nf = go_to_sexp_nf 0 [] *)
(* let to_sexp_ne = go_to_sexp_ne 0 [] *)

(* let pp t = to_sexp t |> Sexp.to_string_hum *)
(* let pp_nf t = to_sexp_nf t |> Sexp.to_string_hum *)
(* let pp_ne t = to_sexp_ne t |> Sexp.to_string_hum *)
