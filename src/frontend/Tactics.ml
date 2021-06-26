open Basis
open Core
open CodeUnit

module RM = RefineMonad
module T = Tactic
module D = Domain
module S = Syntax
module R = Refiner
module CS = ConcreteSyntax
module Sem = Semantics

open Monad.Notation (RM)

let elab_err err =
  let* env = RM.read in
  RM.throw @@ ElabError.ElabError (err, RefineEnv.location env)


let match_goal (tac : _ -> T.Chk.tac RM.m) : T.Chk.tac =
  T.Chk.brule @@
  fun goal ->
  let* tac = tac goal in
  T.Chk.brun tac goal

let rec elim_implicit_connectives : T.Syn.tac -> T.Syn.tac =
  fun tac ->
  T.Syn.rule @@
  let* tm, tp = T.Syn.run @@ T.Syn.whnf ~style:`UnfoldAll tac in
  match tp with
  | D.Sub _ ->
    T.Syn.run @@ elim_implicit_connectives @@ R.Sub.elim @@ T.Syn.rule @@ RM.ret (tm, tp)
  (* The above code only makes sense because I know that the argument to Sub.elim will not be called under a further binder *)
  | D.ElStable _ ->
    T.Syn.run @@ elim_implicit_connectives @@ R.El.elim @@ T.Syn.rule @@ RM.ret (tm, tp)
  | _ ->
    RM.ret (tm, tp)

let rec intro_implicit_connectives : T.Chk.tac -> T.Chk.tac =
  fun tac ->
  T.Chk.whnf ~style:`UnfoldAll @@
  match_goal @@ function
  | D.Sub _, _, _ ->
    RM.ret @@ R.Sub.intro @@ intro_implicit_connectives tac
  | D.ElStable _, _, _ ->
    RM.ret @@ R.El.intro @@ intro_implicit_connectives tac
  | _ ->
    RM.ret tac

let rec intro_subtypes : T.Chk.tac -> T.Chk.tac =
  fun tac ->
  T.Chk.whnf ~style:`UnfoldNone @@
  match_goal @@ function
  | D.Sub _, _, _ ->
    RM.ret @@ R.Sub.intro @@ intro_subtypes tac
  | _ ->
    RM.ret tac

let rec tac_nary_quantifier (quant : ('a, 'b) R.quantifier) cells body =
  match cells with
  | [] -> body
  | (nm, tac) :: cells ->
    quant tac nm @@ fun _ -> tac_nary_quantifier quant cells body

module Elim =
struct
  type case_tac = CS.pat * T.Chk.tac

  let rec find_case (lbl : string) (cases : case_tac list) : (CS.pat_arg list * T.Chk.tac) option =
    match cases with
    | (CS.Pat pat, tac) :: _ when pat.lbl = lbl ->
      Some (pat.args, tac)
    | _ :: cases ->
      find_case lbl cases
    | [] ->
      None

  let elim (mot : T.Chk.tac) (cases : case_tac list) (scrut : T.Syn.tac) : T.Syn.tac =
    T.Syn.rule @@
    let* tscrut, ind_tp = T.Syn.run scrut in
    let scrut = T.Syn.rule @@ RM.ret (tscrut, ind_tp) (* only makes sense because because I know 'scrut' won't be used under some binder *) in
    match ind_tp, mot with
    | D.Nat, mot ->
      let* tac_zero : T.Chk.tac =
        match find_case "zero" cases with
        | Some ([], tac) -> RM.ret tac
        | Some _ -> elab_err ElabError.MalformedCase
        | None -> RM.ret @@ R.Hole.unleash_hole @@ Some "zero"
      in
      let* tac_suc =
        match find_case "suc" cases with
        | Some ([`Simple nm_z], tac) ->
          RM.ret @@ R.Pi.intro ~ident:nm_z @@ fun _ -> R.Pi.intro @@ fun _ -> tac
        | Some ([`Inductive (nm_z, nm_ih)], tac) ->
          RM.ret @@ R.Pi.intro ~ident:nm_z @@ fun _ -> R.Pi.intro ~ident:nm_ih @@ fun _ -> tac
        | Some _ -> elab_err ElabError.MalformedCase
        | None -> RM.ret @@ R.Hole.unleash_hole @@ Some "suc"
      in
      T.Syn.run @@ R.Nat.elim mot tac_zero tac_suc scrut
    | D.Circle, mot ->
      let* tac_base : T.Chk.tac =
        match find_case "base" cases with
        | Some ([], tac) -> RM.ret tac
        | Some _ -> elab_err ElabError.MalformedCase
        | None -> RM.ret @@ R.Hole.unleash_hole @@ Some "base"
      in
      let* tac_loop =
        match find_case "loop" cases with
        | Some ([`Simple nm_x], tac) ->
          RM.ret @@ R.Pi.intro ~ident:nm_x @@ fun _ -> tac
        | Some _ -> elab_err ElabError.MalformedCase
        | None -> RM.ret @@ R.Hole.unleash_hole @@ Some "loop"
      in
      T.Syn.run @@ R.Circle.elim mot tac_base tac_loop scrut
    | _ ->
      RM.with_pp @@ fun ppenv ->
      let* tp = RM.quote_tp ind_tp in
      elab_err @@ ElabError.CannotEliminate (ppenv, tp)

  let assert_simple_inductive =
    function
    | D.Nat ->
      RM.ret ()
    | D.Circle ->
      RM.ret ()
    | tp ->
      RM.with_pp @@ fun ppenv ->
      let* tp = RM.quote_tp tp in
      elab_err @@ ElabError.ExpectedSimpleInductive (ppenv, tp)

  let lam_elim cases : T.Chk.tac =
    match_goal @@ fun (tp, _, _) ->
    match tp with
    | D.Pi (_, _, fam) ->
      let mot_tac : T.Chk.tac =
        R.Pi.intro @@ fun var -> (* of inductive type *)
        T.Chk.brule @@ fun _goal ->
        let* fib = RM.lift_cmp @@ Sem.inst_tp_clo fam @@ D.ElIn (T.Var.con var) in
        let* tfib = RM.quote_tp fib in
        match tfib with
        | S.El code ->
          RM.ret code
        | _ ->
          RM.expected_connective `El fib
      in
      RM.ret @@
      R.Pi.intro @@ fun x ->
      T.Chk.syn @@
      elim mot_tac cases @@
      R.El.elim @@ T.Var.syn x
    | _ ->
      RM.expected_connective `Pi tp
end
