module D = Domain
module S = Syntax
module CS = ConcreteSyntax
module Env = ElabEnv
module Err = ElabError
module EM = ElabBasics
module Nbe = Nbe.Monadic

open Monad.Notation (EM)

type tp_tac = D.tp EM.m
type chk_tac = D.tp -> S.t EM.m
type syn_tac = (S.t * D.tp) EM.m

let elab_err err = raise @@ Err.ElabError err

let rec int_to_term = 
  function
  | 0 -> S.Zero
  | n -> S.Suc (int_to_term (n - 1))

let unleash_hole name : chk_tac = 
  fun tp ->
  let rec go_tp : Env.cell list -> S.tp m =
    function
    | [] ->
      EM.lift_qu @@ Nbe.quote_tp tp
    | (D.Nf cell, name) :: cells -> 
      let+ base = EM.lift_qu @@ Nbe.quote_tp cell.tp
      and+ fam = EM.push_var name cell.tp @@ go_tp cells in
      S.Pi (base, fam)
  in

  let rec go_tm ne : Env.cell list -> D.ne =
    function 
    | [] -> ne
    | (nf, _) :: cells ->
      D.Ap (go_tm ne cells, nf)
  in

  let* ne = 
    let* env = EM.read in
    EM.globally @@ 
    let+ sym = 
      let* tp = go_tp @@ Env.locals env in
      let* vtp = EM.lift_ev @@ Nbe.eval_tp tp in
      EM.add_global name vtp None 
    in
    go_tm (D.Global sym) @@ Env.locals env 
  in

  EM.lift_qu @@ Nbe.quote_ne ne 


let pi_intro name tac_body : chk_tac = 
  function
  | D.Pi (base, fam) ->
    EM.push_var name base @@ 
    let* var = EM.get_local 0 in
    let* fib = EM.lift_cmp @@ Nbe.inst_tp_clo fam [var] in
    let+ t = tac_body fib in
    S.Lam t
  | tp ->
    elab_err @@ Err.ExpectedConnective (`Pi, tp)

let sg_intro tac_fst tac_snd : chk_tac = 
  function
  | D.Sg (base, fam) ->
    let* tfst = tac_fst base in
    let* vfst = EM.lift_ev @@ Nbe.eval tfst in
    let* fib = EM.lift_cmp @@ Nbe.inst_tp_clo fam [vfst] in
    let+ tsnd = tac_snd fib in
    S.Pair (tfst, tsnd)
  | tp ->
    elab_err @@ Err.ExpectedConnective (`Sg, tp)

let id_intro : chk_tac =
  function
  | D.Id (tp, l, r) ->
    let+ () = EM.equate tp l r
    and+ t = EM.lift_qu @@ Nbe.quote tp l in
    S.Refl t
  | tp ->
    elab_err @@ Err.ExpectedConnective (`Id, tp)

let literal n : chk_tac = 
  function
  | D.Nat ->
    EM.ret @@ int_to_term n
  | tp ->
    elab_err @@ Err.ExpectedConnective (`Nat, tp)

let syn_to_chk (tac : syn_tac) : chk_tac =
  fun tp ->
  let* tm, tp' = tac in
  let+ () = EM.equate_tp tp tp' in 
  tm

let lookup_var id : syn_tac =
  let* res = EM.resolve id in
  match res with
  | `Local ix ->
    let* tp = EM.get_local_tp ix in
    EM.ret (S.Var ix, tp)
  | `Global sym -> 
    let* D.Nf {tp; _} = EM.get_global sym in 
    EM.ret (S.Global sym, tp)
  | `Unbound -> 
    elab_err @@ Err.UnboundVariable id


let apply tac_fun tac_arg : syn_tac = 
  let* tfun, tp = tac_fun in
  let* base, fam = EM.dest_pi tp in
  let* targ = tac_arg base in
  let* varg = EM.lift_ev @@ Nbe.eval targ in
  let+ fib = EM.lift_cmp @@ Nbe.inst_tp_clo fam [varg] in
  S.Ap (tfun, targ), fib

module Tactic = 
struct
  let rec tac_multilam names tac_body =
    match names with
    | [] -> tac_body
    | name :: names -> 
      pi_intro (Some name) @@ 
      tac_multilam names tac_body

  let rec tac_multi_apply tac_fun =
    function
    | [] -> tac_fun
    | tac :: tacs ->
      tac_multi_apply (apply tac_fun tac) tacs
end

include Tactic