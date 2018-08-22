open Sexplib

type env = t list
and clos =
    Clos of {term : Syntax.t; env : env}
  | ConstClos of t
and clos2 = Clos2 of {term : Syntax.t; env : env}
and tick_clos =
    TickClos of {term : Syntax.t; env : env}
  | ConstTickClos of t
and t =
  | Lam of t * clos
  | Neutral of {tp : t; term : ne}
  | Nat
  | Zero
  | Suc of t
  | Pi of t * clos
  | Sig of t * clos
  | Pair of t * t
  | Later of tick_clos
  | Next of tick_clos
  | DFix of t * clos
  | Fold of Syntax.uni_level * t * clos * t * t * int
  | Tick of int (* DeBruijn level *)
  | Bullet
  | Box of t
  | Shut of t
  | Uni of Syntax.uni_level
and ne =
  | Var of int (* DeBruijn levels for variables *)
  | Ap of ne * nf
  | Fst of ne
  | Snd of ne
  | Prev of ne * int option (* None = Bullet, Some i = Tick i *)
  | Fix of t * clos * int
  | Unfold of Syntax.uni_level * t * clos * t * t * int
  | Open of ne
  | NRec of clos * nf * clos2 * ne
and nf =
  | Normal of {tp : t; term : t}

let mk_var tp lev = Neutral {tp; term = Var lev}

let tick_to_term = function
    None -> Bullet
  | Some i -> Tick i

let term_to_tick = function
    Bullet -> None
  | Tick i -> Some i
  | _ -> raise (Invalid_argument "Not a tick-like term in term_to_tick")

let rec int_of_syn = function
  | Zero -> Some 0
  | Suc t ->
    begin
      match int_of_syn t with
      | Some i -> Some (i + 1)
      | None -> None
    end
  | _ -> None

let rec go_to_sexp size env = function
  | Nat -> Sexp.Atom "Nat"
  | Zero -> Sexp.Atom "zero"
  | Suc t ->
    begin
      match int_of_syn t with
      | Some i -> Sexp.Atom (string_of_int (i + 1))
      | None -> Sexp.List [Sexp.Atom "suc"; go_to_sexp size env t]
    end
  | Pi (src, dest) ->
    Sexp.List
      [Sexp.Atom "Pi";
       go_to_sexp size env src;
       go_to_sexp_clos size env dest]
  | Lam (tp, t) ->
    Sexp.List [Sexp.Atom "lam"; go_to_sexp size env tp; go_to_sexp_clos size env t]
  | Sig (fst, snd) ->
    Sexp.List
      [Sexp.Atom "Sig";
       go_to_sexp size env fst;
       go_to_sexp_clos size env snd]
  | Pair (t1, t2) ->
    Sexp.List [Sexp.Atom "pair"; go_to_sexp size env t1; go_to_sexp size env t2]
  | Uni i -> Sexp.List [Sexp.Atom "U"; Sexp.Atom (string_of_int i)]
  | Later t ->
    Sexp.List [Sexp.Atom "Later"; go_to_sexp_tick_clos size env t]
  | Next t -> Sexp.List [Sexp.Atom "Next"; go_to_sexp_tick_clos size env t]
  | Bullet -> Sexp.Atom "<>"
  | Box t -> Sexp.List [Sexp.Atom "Box"; go_to_sexp size env t]
  | Shut t -> Sexp.List [Sexp.Atom "shut"; go_to_sexp size env t]
  | DFix (tp, body) ->
    Sexp.List
      [Sexp.Atom "DFix";
       go_to_sexp size env tp;
       go_to_sexp_clos size env body]
  | Fold (uni, idx_tp, body, idx, t, tick) ->
    Sexp.List
      [Sexp.Atom "fold";
       Sexp.Atom (string_of_int uni);
       go_to_sexp size env idx_tp;
       go_to_sexp_clos size env body;
       go_to_sexp size env idx;
       go_to_sexp size env t;
       go_to_sexp size env (Tick tick)]
  | Tick i ->
    if i >= size
    then Sexp.Atom ("x" ^ string_of_int i)
    else List.nth env i
  | Neutral {tp; term} -> Sexp.List [Sexp.Atom "up"; go_to_sexp size env tp; go_to_sexp_ne size env term]

and go_to_sexp_clos size env = function
  | ConstClos t -> Sexp.List [Sexp.Atom "_"; go_to_sexp size env t]
  | Clos body ->
    let var = Sexp.Atom ("x" ^ string_of_int size) in
    let new_env = var :: List.map (go_to_sexp size env) body.env |> List.rev in
    Sexp.List [var; Syntax.to_sexp new_env body.term]

and go_to_sexp_tick_clos size env = function
  | ConstTickClos t -> Sexp.List [Sexp.Atom "_"; go_to_sexp size env t]
  | TickClos body ->
    let var = Sexp.Atom ("x" ^ string_of_int size) in
    let new_env = var :: List.map (go_to_sexp size env) body.env |> List.rev in
    Sexp.List [var; Syntax.to_sexp new_env body.term]

and go_to_sexp_ne size env = function
  | Var i ->
    if i >= size
    then Sexp.Atom ("x" ^ string_of_int i)
    else List.nth env i
  | Ap (f, a) ->
    Sexp.List [Sexp.Atom "ap"; go_to_sexp_ne size env f; go_to_sexp_nf size env a]
  | Fst p -> Sexp.List [Sexp.Atom "fst"; go_to_sexp_ne size env p]
  | Snd p -> Sexp.List [Sexp.Atom "snd"; go_to_sexp_ne size env p]
  | Prev (ne, i) ->
    Sexp.List
      [Sexp.Atom "prev";
       go_to_sexp_ne size env ne;
       tick_to_term i |> go_to_sexp size env]
  | Fix (tp, clos, i) ->
    Sexp.List
      [Sexp.Atom "prev";
       go_to_sexp size env (DFix (tp, clos));
       go_to_sexp size env (Tick i)]
  | Unfold (uni, a, body, idx, t, i) ->
    Sexp.List
      [Sexp.Atom "unfold";
       Sexp.Atom (string_of_int uni);
       go_to_sexp size env a;
       go_to_sexp_clos size env body;
       go_to_sexp size env idx;
       go_to_sexp size env t;
       go_to_sexp size env (Tick i)]
  | Open t -> Sexp.List [Sexp.Atom "open"; go_to_sexp_ne size env t]
  | NRec (motive, zero, Clos2 suc, n) ->
    let suc_var1 = Sexp.Atom ("x" ^ string_of_int (size + 1)) in
    let suc_var2 = Sexp.Atom ("x" ^ string_of_int (size + 2)) in
    let senv = suc_var2 :: suc_var1 :: List.map (go_to_sexp size env) suc.env |> List.rev in
    Sexp.List
      [Sexp.Atom "nrec";
       go_to_sexp_clos size env motive;
       go_to_sexp_nf size env zero;
       Sexp.List [suc_var1; suc_var2; Syntax.to_sexp senv suc.term];
       go_to_sexp_ne size env n]

and go_to_sexp_nf size env (Normal {tp; term}) =
  Sexp.List
    [Sexp.Atom "down";
     go_to_sexp size env tp;
     go_to_sexp size env term]

let to_sexp = go_to_sexp 0 []
let to_sexp_nf = go_to_sexp_nf 0 []
let to_sexp_ne = go_to_sexp_ne 0 []

let pp t = to_sexp t |> Sexp.to_string_hum
let pp_nf t = to_sexp_nf t |> Sexp.to_string_hum
let pp_ne t = to_sexp_ne t |> Sexp.to_string_hum
