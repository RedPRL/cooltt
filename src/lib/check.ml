module D = Domain
module Syn = Syntax
type env_entry =
    Term of {term : D.t; tp : D.t; locks : int}
  | TopLevel of {term : D.t; tp : D.t}
type env = env_entry list

let add_term ~term ~tp env = Term {term; tp; locks = 0} :: env

type error =
    Cannot_synth_term of Syn.t
  | Using_locked_variable
  | Type_mismatch of D.t * D.t
  | Expecting_universe of D.t
  | Misc of string

let pp_error fmt = function
  | Cannot_synth_term t ->
    Format.fprintf fmt "@[Cannot synthesize the type of: @[";
    Syn.pp fmt t;
    Format.fprintf fmt "@]@]";
  | Using_locked_variable -> Format.fprintf fmt "Cannot use a variable behind a lock."
  | Type_mismatch (t1, t2) ->
    Format.fprintf fmt "@[Cannot equate@ @[";
    D.pp fmt t1;
    Format.fprintf fmt "@]@ with@ @[";
    D.pp fmt t2;
    Format.fprintf fmt "@]";
  | Expecting_universe d ->
    Format.fprintf fmt "@[Expected some universe but found@ @[";
    D.pp fmt d;
    Format.fprintf fmt "@]@]"
  | Misc s -> Format.pp_print_string fmt s

exception Type_error of error

let tp_error e = raise (Type_error e)

let env_to_sem_env =
  List.map
    (function
      | TopLevel {term; _} -> term
      | Term {term; _} -> term)

module S = Set.Make(struct type t = int;; let compare = compare end)

let strip_env =
  let go = function
    | TopLevel r -> TopLevel r
    | Term r -> Term {r with locks = 0} in
  List.map go

let apply_lock =
  List.map
    (function
      | TopLevel r -> TopLevel r
      | Term t -> Term {t with locks = t.locks + 1})

let get_var env n = match List.nth env n with
  | Term {term = _; tp; locks = 0} -> tp
  | TopLevel {tp; _} -> tp
  | Term _ -> tp_error Using_locked_variable

let assert_subtype size t1 t2 =
  if Nbe.check_subtype size t1 t2
  then ()
  else tp_error (Type_mismatch (t1, t2))

let rec check ~env ~size ~term ~tp =
  match term with
  | Syn.Let (def, body) ->
    let def_tp = synth ~env ~size ~term:def in
    let def_val = Nbe.eval def (env_to_sem_env env) in
    check ~env:(add_term ~term:def_val ~tp:def_tp env) ~size:(size + 1) ~term:body ~tp
  | Nat ->
    begin
      match tp with
      | D.Uni _ -> ()
      | t -> tp_error (Expecting_universe t)
    end
  | Pi (l, r) | Sig (l, r) ->
    check ~env ~size ~term:l ~tp;
    let l_sem = Nbe.eval l (env_to_sem_env env) in
    let var = D.mk_var l_sem size in
    check ~env:(add_term ~term:var ~tp:l_sem env) ~size ~term:r ~tp
  | Lam body ->
    begin
      match tp with
      | D.Pi (arg_tp, clos) ->
        let var = D.mk_var arg_tp size in
        let dest_tp = Nbe.do_clos clos var in
        check ~env:(add_term ~term:var ~tp:arg_tp env) ~size:(size + 1) ~term:body ~tp:dest_tp;
      | t -> tp_error (Misc ("Expecting Pi but found\n" ^ D.show t))
    end
  | Pair (left, right) ->
    begin
      match tp with
      | D.Sig (left_tp, right_tp) ->
        check ~env ~size ~term:left ~tp:left_tp;
        let left_sem = Nbe.eval left (env_to_sem_env env) in
        check ~env ~size ~term:right ~tp:(Nbe.do_clos right_tp left_sem)
      | t -> tp_error (Misc ("Expecting Sig but found\n" ^ D.show t))
    end
  | Box term -> check ~env:(apply_lock env) ~size ~term ~tp
  | Shut term ->
    begin
      match tp with
      | Box tp -> check ~env:(apply_lock env) ~size ~term ~tp
      | t -> tp_error (Misc ("Expecting Box but found\n" ^ D.show t))
    end
  | Uni i ->
    begin
      match tp with
      | Uni j when i < j -> ()
      | t ->
        let msg =
          "Expecting universe over " ^ string_of_int i ^ " but found\n" ^ D.show t in
        tp_error (Misc msg)
    end
  | term -> assert_subtype size (synth ~env ~size ~term) tp

and synth ~env ~size ~term =
  match term with
  | Syn.Var i -> get_var env i
  | Check (term, tp') ->
    let tp = Nbe.eval tp' (env_to_sem_env env) in
    check ~env ~size ~term ~tp;
    tp
  | Zero -> D.Nat
  | Suc term -> check ~env ~size ~term ~tp:Nat; D.Nat
  | Fst p ->
    begin
      match synth ~env ~size ~term:p with
      | Sig (left_tp, _) -> left_tp
      | t -> tp_error (Misc ("Expecting Sig but found\n" ^ D.show t))
    end
  | Snd p ->
    begin
      match synth ~env ~size ~term:p with
      | Sig (_, right_tp) ->
        let proj = Nbe.eval (Fst p) (env_to_sem_env env) in
        Nbe.do_clos right_tp proj
      | t -> tp_error (Misc ("Expecting Sig but found\n" ^ D.show t))
    end
  | Ap (f, a) ->
    begin
      match synth ~env ~size ~term:f with
      | Pi (src, dest) ->
        check ~env ~size ~term:a ~tp:src;
        let a_sem = Nbe.eval a (env_to_sem_env env) in
        Nbe.do_clos dest a_sem
      | t -> tp_error (Misc ("Expecting Pi but found\n" ^ D.show t))
    end
  | NRec (mot, zero, suc, n) ->
    check ~env ~size ~term:n ~tp:Nat;
    let var = D.mk_var Nat size in
    check_tp ~env:(add_term ~term:var ~tp:Nat env) ~size:(size + 1) ~term:mot;
    let sem_env = env_to_sem_env env in
    let zero_tp = Nbe.eval mot (Zero :: sem_env) in
    let ih_tp = Nbe.eval mot (var :: sem_env) in
    let ih_var = D.mk_var ih_tp (size + 1) in
    let suc_tp = Nbe.eval mot (Suc var :: sem_env) in
    check ~env ~size ~term:zero ~tp:zero_tp;
    check
      ~env:(add_term ~term:var ~tp:Nat env |> add_term ~term:ih_var ~tp:ih_tp)
      ~size:(size + 2)
      ~term:suc
      ~tp:suc_tp;
    Nbe.eval mot (Nbe.eval n sem_env :: sem_env)
  | Open term ->
    let env = strip_env env in
    begin
      match synth ~env ~size ~term with
      | Box tp -> tp
      | t -> tp_error (Misc ("Expecting Box but found\n" ^ D.show t))
    end
  | _ -> tp_error (Cannot_synth_term term)

and check_tp ~env ~size ~term =
  match term with
  | Syn.Nat -> ()
  | Uni _ -> ()
  | Box term -> check_tp ~env:(apply_lock env) ~size ~term
  | Pi (l, r) | Sig (l, r) ->
    check_tp ~env ~size ~term:l;
    let l_sem = Nbe.eval l (env_to_sem_env env) in
    let var = D.mk_var l_sem size in
    check_tp ~env:(add_term ~term:var ~tp:l_sem env) ~size:(size + 1) ~term:r
  | Let (def, body) ->
    let def_tp = synth ~env ~size ~term:def in
    let def_val = Nbe.eval def (env_to_sem_env env) in
    check_tp ~env:(add_term ~term:def_val ~tp:def_tp env) ~size:(size + 1) ~term:body
  | term ->
    begin
      match synth ~env ~size ~term with
      | D.Uni _ -> ()
      | t -> tp_error (Expecting_universe t)
    end
