(* This file implements the semantic type-checking algorithm described in the paper. *)
module D = Domain
module Syn = Syntax
type error =
    Cannot_synth_term of Syn.t
  | Type_mismatch of D.t * D.t
  | Expecting_universe of D.t
  | Misc of string

exception Type_error of error

let tp_error e = raise (Type_error e)

module Env : 
sig
  type entry =
      Term of {term : Domain.t; tp : Domain.t}
    | TopLevel of {term : Domain.t; tp : Domain.t}

  type t
  val size : t -> int

  val empty : t
  val add_entry : entry -> t -> t
  val add_term : term:Domain.t -> tp:Domain.t -> t -> t
  val to_sem_env : t -> Domain.env
  val get_var : t -> int -> Domain.t
  val get_entry : t -> int -> entry
end = 
struct
  type entry =
      Term of {term : D.t; tp : D.t}
    | TopLevel of {term : D.t; tp : D.t}

  type t = {entries : entry list; size : int}

  let size env = env.size 

  let empty = {entries = []; size = 0}

  let add_entry entry env =
    {entries = entry :: env.entries; size = env.size + 1}

  let add_term ~term ~tp = add_entry @@ Term {term; tp}

  let to_sem_env env =
    List.map
      (function
        | TopLevel {term; _} -> term
        | Term {term; _} -> term)
      env.entries

  let get_var env n = 
    match List.nth env.entries n with
    | Term {term = _; tp} -> tp
    | TopLevel {tp; _} -> tp

  let get_entry env n = List.nth env.entries n

end

type env = Env.t

let pp_error fmt = function
  | Cannot_synth_term t ->
    Format.fprintf fmt "@[<v> Cannot synthesize the type of: @[<hov 2>  ";
    Syn.pp fmt t;
    Format.fprintf fmt "@]@]@,"
  | Type_mismatch (t1, t2) ->
    Format.fprintf fmt "@[<v>Cannot equate@,@[<hov 2>  ";
    D.pp fmt t1;
    Format.fprintf fmt "@]@ with@,@[<hov 2>  ";
    D.pp fmt t2;
    Format.fprintf fmt "@]@]@,"
  | Expecting_universe d ->
    Format.fprintf fmt "@[<v>Expected some universe but found@ @[<hov 2>";
    D.pp fmt d;
    Format.fprintf fmt "@]@]@,"
  | Misc s -> Format.pp_print_string fmt s


let assert_equal size t1 t2 tp =
  if Nbe.equal_nf size (D.Nf {tp; term = t1}) (D.Nf {tp; term = t2})
  then ()
  else tp_error (Type_mismatch (t1, t2))

let rec check ~env ~term ~tp =
  match term with
  | Syn.Let (def, body) ->
    let def_tp = synth ~env ~term:def in
    let def_val = Nbe.eval def (Env.to_sem_env env) in
    check ~env:(Env.add_term ~term:def_val ~tp:def_tp env) ~term:body ~tp
  | Refl term ->
    begin
      match tp with
      | D.Id (tp, left, right) ->
        check ~env ~term ~tp;
        let term = Nbe.eval term (Env.to_sem_env env) in
        assert_equal (Env.size env) term left tp;
        assert_equal (Env.size env) term right tp
      | t -> tp_error (Misc ("Expecting Id but found\n" ^ D.show t))
    end
  | Lam body ->
    begin
      match tp with
      | D.Pi (arg_tp, clos) ->
        let var = D.mk_var arg_tp (Env.size env) in
        let dest_tp = Nbe.do_tp_clos clos var in
        check ~env:(Env.add_term ~term:var ~tp:arg_tp env) ~term:body ~tp:dest_tp;
      | t -> tp_error (Misc ("Expecting Pi but found\n" ^ D.show t))
    end
  | Pair (left, right) ->
    begin
      match tp with
      | D.Sg (left_tp, right_tp) ->
        check ~env ~term:left ~tp:left_tp;
        let left_sem = Nbe.eval left (Env.to_sem_env env) in
        check ~env ~term:right ~tp:(Nbe.do_tp_clos right_tp left_sem)
      | t -> tp_error (Misc ("Expecting Sg but found\n" ^ D.show t))
    end
  | _ ->
    let tp' = synth ~env ~term in 
    if Nbe.equal_tp (Env.size env) tp' tp
    then ()
    else tp_error (Type_mismatch (tp', tp))

and synth ~env ~term =
  match term with
  | Syn.Var i -> Env.get_var env i
  | Check (term, tp') ->
    let tp = Nbe.eval_tp tp' (Env.to_sem_env env) in
    check ~env ~term ~tp;
    tp
  | Zero -> D.Nat
  | Suc term -> check ~env ~term ~tp:Nat; D.Nat
  | Fst p ->
    begin
      match synth ~env ~term:p with
      | Sg (left_tp, _) -> left_tp
      | t -> tp_error (Misc ("Expecting Sg but found\n" ^ D.show t))
    end
  | Snd p ->
    begin
      match synth ~env ~term:p with
      | Sg (_, right_tp) ->
        let proj = Nbe.eval (Fst p) (Env.to_sem_env env) in
        Nbe.do_tp_clos right_tp proj
      | t -> tp_error (Misc ("Expecting Sg but found\n" ^ D.show t))
    end
  | Ap (f, a) ->
    begin
      match synth ~env ~term:f with
      | Pi (src, dest) ->
        check ~env ~term:a ~tp:src;
        let a_sem = Nbe.eval a (Env.to_sem_env env) in
        Nbe.do_tp_clos dest a_sem
      | t -> tp_error (Misc ("Expecting Pi but found\n" ^ D.show t))
    end
  | NRec (mot, zero, suc, n) ->
    check ~env ~term:n ~tp:Nat;
    let var = D.mk_var Nat (Env.size env) in
    check_tp ~env:(Env.add_term ~term:var ~tp:Nat env) ~term:mot;
    let sem_env = Env.to_sem_env env in
    let zero_tp = Nbe.eval_tp mot (Zero :: sem_env) in
    let ih_tp = Nbe.eval_tp mot (var :: sem_env) in
    let ih_var = D.mk_var ih_tp (Env.size env + 1) in
    let suc_tp = Nbe.eval_tp mot (Suc var :: sem_env) in
    check ~env ~term:zero ~tp:zero_tp;
    check
      ~env:(Env.add_term ~term:var ~tp:Nat env |> Env.add_term ~term:ih_var ~tp:ih_tp)
      ~term:suc
      ~tp:suc_tp;
    Nbe.eval_tp mot (Nbe.eval n sem_env :: sem_env)
  | J (mot, refl, eq) ->
    let eq_tp = synth ~env ~term:eq in
    begin
      let sem_env = Env.to_sem_env env in
      match eq_tp with
      | D.Id (tp', left, right) ->
        let mot_var1 = D.mk_var tp' (Env.size env) in
        let mot_var2 = D.mk_var tp' (Env.size env + 1) in
        let mot_var3 = D.mk_var (D.Id (tp', mot_var1, mot_var2)) (Env.size env + 1) in
        let mot_env =
          Env.add_term ~term:mot_var1 ~tp:tp' env
          |> Env.add_term ~term:mot_var2 ~tp:tp'
          |> Env.add_term ~term:mot_var3 ~tp:(D.Id (tp', mot_var1, mot_var2)) in
        check_tp ~env:mot_env ~term:mot;
        let refl_var = D.mk_var tp' (Env.size env) in
        let refl_tp = Nbe.eval_tp mot (D.Refl refl_var :: refl_var :: refl_var :: sem_env) in
        check ~env:(Env.add_term ~term:refl_var ~tp:tp' env) ~term:refl ~tp:refl_tp;
        Nbe.eval_tp mot (Nbe.eval eq sem_env :: right :: left :: sem_env)
      | t -> tp_error (Misc ("Expecting Id but found\n" ^ D.show t))
    end
  | _ -> tp_error (Cannot_synth_term term)

and check_tp ~env ~term =
  match term with
  | Nat -> ()
  | Pi (l, r) | Sg (l, r) ->
    check_tp ~env ~term:l;
    let l_sem = Nbe.eval_tp l (Env.to_sem_env env) in
    let var = D.mk_var l_sem (Env.size env) in
    check_tp ~env:(Env.add_term ~term:var ~tp:l_sem env) ~term:r
  | Id (tp, l, r) ->
    check_tp ~env ~term:tp;
    let tp = Nbe.eval_tp tp (Env.to_sem_env env) in
    check ~env ~term:l ~tp;
    check ~env ~term:r ~tp
