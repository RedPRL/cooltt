module CS = ConcreteSyntax
module S = Syntax
module D = Domain
module EM = ElabMonad
module Env = ElabEnv
module Err = ElabError

open Monad.Notation (EM)

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

let quote tp v =
  EM.quote @@ D.Nf {tp; term = v}

let lookup_var id =
  let* res = EM.resolve id in
  match res with
  | `Local ix ->
    let* tp = EM.get_local ix in
    EM.ret (S.Var ix, tp)
  | `Global sym -> 
    let* D.Nf {tp; _} = EM.get_global sym in 
    EM.ret (S.Global sym, tp)
  | `Unbound -> 
    EM.throw @@ Err.ElabError (Err.UnboundVariable id)

let dest_pi = 
  function
  | D.Pi (base, fam) -> EM.ret (base, fam)
  | tp -> EM.throw @@ Err.ElabError (Err.ExpectedPiType tp)

let rec check_tp : CS.t -> S.tp EM.m = 
  function
  | CS.Pi (cells, body) -> check_pi_tp cells body
  | CS.Sg (cells, body) -> check_sg_tp cells body
  | CS.Nat -> EM.ret S.Nat
  | CS.Id (tp, l, r) ->
    let* tp = check_tp tp in
    let* vtp = eval_tp tp in
    let+ l = check_tm l vtp
    and+ r = check_tm r vtp in
    S.Id (tp, l, r)
  | tp -> EM.throw @@ Err.ElabError (Err.InvalidTypeExpression tp)

and check_tm : CS.t -> D.tp -> S.t EM.m =
  fun cs tp ->
  match cs, tp with
  | CS.Refl _, D.Id (tp, l, r) ->
    let+ () = equate tp l r
    and+ t = quote tp l in
    S.Refl t
  | CS.Lit n, D.Nat -> EM.ret @@ int_to_term n
  | _ ->
    let* tm, tp' = synth_tm cs in
    let+ () = equate_tp tp tp' in
    tm

and synth_tm : CS.t -> (S.t * D.tp) EM.m = 
  function
  | CS.Var id -> lookup_var id
  | CS.Ap (t, ts) ->
    let* t, tp = synth_tm t in
    synth_ap t tp ts
  | _ -> failwith "TODO"

and synth_ap head head_tp spine =
  match spine with
  | [] -> EM.ret (head, head_tp)
  | CS.Term arg :: spine ->
    let* base, fam = dest_pi head_tp in
    let* arg = check_tm arg base in
    let* varg = eval_tm arg in
    let* fib = inst_tp_clo fam varg in
    synth_ap (S.Ap (head, arg)) fib spine

and check_sg_tp cells body =
  match cells with
  | [] -> check_tp body
  | Cell cell :: cells ->
    let* base = check_tp cell.tp in
    let* vbase = eval_tp base in
    let+ fam = EM.push_var cell.name vbase @@ check_sg_tp cells body in
    S.Sg (base, fam)

and check_pi_tp cells body =
  match cells with
  | [] -> check_tp body
  | Cell cell :: cells ->
    let* base = check_tp cell.tp in
    let* vbase = eval_tp base in
    let+ fam = EM.push_var cell.name vbase @@ check_pi_tp cells body in
    S.Pi (base, fam)