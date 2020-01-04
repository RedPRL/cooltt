module D = Domain
module S = Syntax
module EM = ElabMonad
module CS = ConcreteSyntax
module Env = ElabEnv
module Err = ElabError

open Monad.Notation (EM)

type tp_tac = D.tp EM.m
type chk_tac = D.tp -> S.t EM.m
type syn_tac = (S.t * D.tp) EM.m

module Util = 
struct
  let rec int_to_term = 
    function
    | 0 -> S.Zero
    | n -> S.Suc (int_to_term (n - 1))

  let read_sem_env =
    let+ env = EM.read in
    Env.to_sem_env env

  let eval_tp tp =
    let* st = EM.get in
    let* sem_env = read_sem_env in
    match Nbe.eval_tp st sem_env tp with
    | v -> EM.ret v
    | exception exn -> EM.throw exn

  let eval_tm tp =
    let* st = EM.get in
    let* sem_env = read_sem_env in
    match Nbe.eval st sem_env tp with
    | v -> EM.ret v
    | exception exn -> EM.throw exn

  let inst_tp_clo clo v =
    let* st = EM.get in
    match Nbe.do_tp_clo st clo v with
    | v -> EM.ret v
    | exception exn -> EM.throw exn

  let equate tp l r =
    let* st = EM.get in
    let* env = EM.read in
    match
      Nbe.equal_nf st (Env.size env)
        (D.Nf {tp; term = l})
        (D.Nf {tp; term = r})
    with
    | true -> EM.ret ()
    | false -> EM.throw @@ Err.ElabError (Err.ExpectedEqual (tp, l, r))

  let equate_tp tp tp' =
    let* st = EM.get in
    let* env = EM.read in
    match Nbe.equal_tp st (Env.size env) tp tp' with
    | true -> EM.ret ()
    | false -> EM.throw @@ Err.ElabError (Err.ExpectedEqualTypes (tp, tp'))

  let dest_pi = 
    function
    | D.Pi (base, fam) -> EM.ret (base, fam)
    | tp -> EM.throw @@ Err.ElabError (Err.ExpectedConnective (`Pi, tp))
end 

include Util


let unleash_hole name tp = 
  let rec go_tp : Env.cell list -> S.tp m =
    function
    | [] ->
      EM.quote_tp tp
    | (D.Nf cell, name) :: cells -> 
      let+ base = EM.quote_tp cell.tp
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
      let* vtp = eval_tp tp in
      EM.add_global name vtp None 
    in
    go_tm (D.Global sym) @@ Env.locals env 
  in

  EM.quote_ne ne


let pi_intro name tac_body = 
  function
  | D.Pi (base, fam) ->
    EM.push_var name base @@ 
    let* var = EM.get_local 0 in
    let* fib = inst_tp_clo fam var in
    let+ t = tac_body fib in
    S.Lam t
  | tp ->
    EM.throw @@ Err.ElabError (Err.ExpectedConnective (`Pi, tp))

let sg_intro tac_fst tac_snd = 
  function
  | D.Sg (base, fam) ->
    let* tfst = tac_fst base in
    let* vfst = eval_tm tfst in
    let* fib = inst_tp_clo fam vfst in
    let+ tsnd = tac_snd fib in
    S.Pair (tfst, tsnd)
  | tp ->
    EM.throw @@ Err.ElabError (Err.ExpectedConnective (`Sg, tp))

let id_intro =
  function
  | D.Id (tp, l, r) ->
    let+ () = equate tp l r
    and+ t = EM.quote tp l in
    S.Refl t
  | tp ->
    EM.throw @@ Err.ElabError (Err.ExpectedConnective (`Id, tp))

let literal n = 
  function
  | D.Nat ->
    EM.ret @@ int_to_term n
  | tp ->
    EM.throw @@ Err.ElabError (Err.ExpectedConnective (`Nat, tp))

let syn_to_chk (tac : syn_tac) : chk_tac =
  fun tp ->
  let* tm, tp' = tac in
  let+ () = equate_tp tp tp' in 
  tm

let lookup_var id =
  let* res = EM.resolve id in
  match res with
  | `Local ix ->
    let* tp = EM.get_local_tp ix in
    EM.ret (S.Var ix, tp)
  | `Global sym -> 
    let* D.Nf {tp; _} = EM.get_global sym in 
    EM.ret (S.Global sym, tp)
  | `Unbound -> 
    EM.throw @@ Err.ElabError (Err.UnboundVariable id)


let apply tac_fun tac_arg : syn_tac = 
  let* tfun, tp = tac_fun in
  let* base, fam = dest_pi tp in
  let* targ = tac_arg base in
  let* varg = eval_tm targ in
  let+ fib = inst_tp_clo fam varg in
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