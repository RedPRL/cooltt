(* This file implements the semantic type-checking algorithm described in the
   paper. *)
module D = Domain
module S = Syntax
module St = ElabState
module Env = ElabEnv


type error =
  | CannotSynthTerm of S.t
  | TypeMismatch of D.tp * D.tp
  | ElementMismatch of D.t * D.t
  | ExpectingUniverse of D.t
  | Misc of string

exception TypeError of error

let tp_error e = raise @@ TypeError e

type env = ElabEnv.t
type state = ElabState.t

let pp_error fmt = function
  | CannotSynthTerm t ->
    Format.fprintf fmt "@[<v> Cannot synthesize the type of: @[<hov 2>  ";
    S.pp fmt t;
    Format.fprintf fmt "@]@]@,"
  | ElementMismatch (t1, t2) ->
    Format.fprintf fmt "@[<v>Cannot equate@,@[<hov 2>  ";
    D.pp fmt t1;
    Format.fprintf fmt "@]@ with@,@[<hov 2>  ";
    D.pp fmt t2;
    Format.fprintf fmt "@]@]@,"
  | TypeMismatch (t1, t2) ->
    Format.fprintf fmt "@[<v>Cannot equate@,@[<hov 2>  ";
    D.pp_tp fmt t1;
    Format.fprintf fmt "@]@ with@,@[<hov 2>  ";
    D.pp_tp fmt t2;
    Format.fprintf fmt "@]@]@,"
  | ExpectingUniverse d ->
    Format.fprintf fmt "@[<v>Expected some universe but found@ @[<hov 2>";
    D.pp fmt d;
    Format.fprintf fmt "@]@]@,"
  | Misc s -> Format.pp_print_string fmt s

let assert_equal st size el1 el2 tp =
  if Nbe.equal_nf st size (D.Nf {tp; el = el1}) (D.Nf {tp; el = el2}) then ()
  else tp_error (ElementMismatch (el1, el2))

let rec check ~st ~env ~term ~tp =
  match term with
  | S.Let (def, body) ->
    let def_tp = synth ~st ~env ~term:def in
    let def_val = Nbe.eval st (Env.to_sem_env env) def in
    check ~st ~env:(Env.push_term None def_val def_tp env) ~term:body ~tp
  | S.Refl term ->
    begin
      match tp with
      | D.Id (tp, left, right) ->
        check ~st ~env ~term ~tp;
        let term = Nbe.eval st (Env.to_sem_env env) term in
        assert_equal st (Env.size env) term left tp;
        assert_equal st (Env.size env) term right tp
      | t -> tp_error @@ Misc ("Expecting Id but found\n" ^ D.show_tp t) 
    end
  | S.Lam body -> 
    begin
      match tp with
      | D.Pi (arg_tp, clo) ->
        let var = D.mk_var arg_tp (Env.size env) in
        let dest_tp = Nbe.inst_tp_clo st clo [var] in
        check ~st
          ~env:(Env.push_term None var arg_tp env)
          ~term:body ~tp:dest_tp
      | t -> tp_error @@ Misc ("Expecting Pi but found\n" ^ D.show_tp t)
    end
  | S.Pair (left, right) ->
    begin
      match tp with
      | D.Sg (left_tp, right_tp) ->
        check ~st ~env ~term:left ~tp:left_tp;
        let left_sem = Nbe.eval st (Env.to_sem_env env) left in
        check ~st ~env ~term:right ~tp:(Nbe.inst_tp_clo st right_tp [left_sem])
      | t -> tp_error @@ Misc ("Expecting Sg but found\n" ^ D.show_tp t)
    end
  | _ ->
    let tp' = synth ~st ~env ~term in
    if Nbe.equal_tp st (Env.size env) tp' tp then ()
    else tp_error (TypeMismatch (tp', tp))

and synth ~st ~env ~term =
  match term with
  | S.Var i -> Env.get_local_tp i env
  | S.Global sym -> 
    let D.Nf {tp; _} = St.get_global sym st in
    tp
  | Check (term, tp') ->
    let tp = Nbe.eval_tp st (Env.to_sem_env env) tp' in
    check ~st ~env ~term ~tp;
    tp
  | S.Zero -> D.Nat
  | S.Suc term ->
    check ~st ~env ~term ~tp:Nat;
    D.Nat
  | S.Fst p -> 
    begin
      match synth ~st ~env ~term:p with
      | Sg (left_tp, _) -> left_tp
      | t -> tp_error @@ Misc ("Expecting Sg but found\n" ^ D.show_tp t) 
    end
  | S.Snd p -> 
    begin
      match synth ~st ~env ~term:p with
      | Sg (_, right_tp) ->
        let proj = Nbe.eval st (Env.to_sem_env env) @@ Fst p in
        Nbe.inst_tp_clo st right_tp [proj]
      | t -> tp_error @@ Misc ("Expecting Sg but found\n" ^ D.show_tp t) 
    end
  | S.Ap (f, a) -> 
    begin
      match synth ~st ~env ~term:f with
      | Pi (src, dest) ->
        check ~st ~env ~term:a ~tp:src;
        let a_sem = Nbe.eval st (Env.to_sem_env env) a in
        Nbe.inst_tp_clo st dest [a_sem]
      | t -> tp_error @@ Misc ("Expecting Pi but found\n" ^ D.show_tp t) 
    end
  | S.NRec (mot, zero, suc, n) ->
    check ~st ~env ~term:n ~tp:Nat;
    let var = D.mk_var Nat (Env.size env) in
    check_tp ~st ~env:(Env.push_term None var Nat env) ~tp:mot;
    let sem_env = Env.to_sem_env env in
    let zero_tp = Nbe.eval_tp st {locals = Zero :: sem_env.locals} mot in
    let ih_tp = Nbe.eval_tp st {locals = var :: sem_env.locals} mot in
    let ih_var = D.mk_var ih_tp (Env.size env + 1) in
    let suc_tp = Nbe.eval_tp st {locals = Suc var :: sem_env.locals} mot in
    check ~st ~env ~term:zero ~tp:zero_tp;
    check ~st
      ~env:
        (Env.push_term None var Nat env
         |> Env.push_term None ih_var ih_tp)
      ~term:suc ~tp:suc_tp;
    Nbe.eval_tp st {locals = (Nbe.eval st sem_env n) :: sem_env.locals} mot
  | S.J (mot, refl, eq) -> 
    let eq_tp = synth ~st ~env ~term:eq in
    let sem_env = Env.to_sem_env env in
    begin
      match eq_tp with
      | D.Id (tp', left, right) ->
        let mot_var1 = D.mk_var tp' (Env.size env) in
        let mot_var2 = D.mk_var tp' (Env.size env + 1) in
        let mot_var3 =
          D.mk_var (D.Id (tp', mot_var1, mot_var2)) (Env.size env + 1)
        in
        let mot_env =
          Env.push_term None mot_var1 tp' env
          |> Env.push_term None mot_var2 tp'
          |> Env.push_term None mot_var3 (D.Id (tp', mot_var1, mot_var2))
        in
        check_tp ~st ~env:mot_env ~tp:mot;
        let refl_var = D.mk_var tp' (Env.size env) in
        let refl_tp =
          Nbe.eval_tp st {locals = D.Refl refl_var :: refl_var :: refl_var :: sem_env.locals} mot
        in
        check ~st
          ~env:(Env.push_term None refl_var tp' env)
          ~term:refl ~tp:refl_tp;
        Nbe.eval_tp st {locals = (Nbe.eval st sem_env eq) :: right :: left :: sem_env.locals} mot
      | t -> tp_error @@ Misc ("Expecting Id but found\n" ^ D.show_tp t)
    end
  | _ -> tp_error (CannotSynthTerm term)

and check_tp ~st ~env ~tp =
  match tp with
  | Nat -> ()
  | Pi (l, r)
  | Sg (l, r) ->
    check_tp ~st ~env ~tp:l;
    let l_sem = Nbe.eval_tp st (Env.to_sem_env env) l in
    let var = D.mk_var l_sem (Env.size env) in
    check_tp ~st ~env:(Env.push_term None var l_sem env) ~tp:r
  | Id (tp, l, r) ->
    check_tp ~st ~env ~tp;
    let tp = Nbe.eval_tp st (Env.to_sem_env env) tp in
    check ~st ~env ~term:l ~tp;
    check ~st ~env ~term:r ~tp