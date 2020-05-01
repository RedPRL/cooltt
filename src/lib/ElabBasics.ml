module CS = ConcreteSyntax
module D = Domain
module S = Syntax
module St = ElabState
module Env = ElabEnv
module Err = ElabError

open CoolBasis
include Monads.ElabM

open Monad.Notation (Monads.ElabM)

let elab_err err = raise @@ Err.ElabError err

let push_var id tp : 'a m -> 'a m =
  scope @@ fun env ->
  let con = D.mk_var tp @@ Env.size env in
  Env.append_con id con tp env

let push_def id tp con : 'a m -> 'a m =
  scope @@ fun env ->
  let tp' = D.Sub (tp, Cof.top, D.const_tm_clo con) in
  let con' = D.SubIn con in
  Env.append_con id con' tp' env

let resolve id =
  let* env = read in
  match Env.resolve_local id env with
  | Some ix -> ret @@ `Local ix
  | None ->
    let* st = get in
    match St.resolve_global id st with
    | Some sym -> ret @@ `Global sym
    | None -> ret `Unbound

let add_global id tp con =
  let* st = get in
  let sym, st' = St.add_global id tp con st in
  let* () = set st' in
  ret sym

let add_flex_global tp =
  let* st = get in
  let sym, st' = St.add_flex_global tp st in
  let* () = set st' in
  ret sym

let get_global sym : (D.tp * D.con) m =
  let* st = get in
  match St.get_global sym st with
  | tp, con -> ret (tp, con)
  | exception exn -> throw exn

let get_local_tp ix =
  let* env = read in
  match Env.get_local_tp ix env with
  | tp -> ret tp
  | exception exn -> throw exn


let get_local ix =
  let* env = read in
  match Env.get_local ix env with
  | tp -> ret tp
  | exception exn -> throw exn

let equate tp l r =
  let* env = read in
  let* res = lift_qu @@ Nbe.equal_con tp l r in
  if res then ret () else
    let* ttp = lift_qu @@ Nbe.quote_tp tp in
    let* tl = lift_qu @@ Nbe.quote_con tp l in
    let* tr = lift_qu @@ Nbe.quote_con tp r in
    elab_err @@ Err.ExpectedEqual (Env.pp_env env, ttp, tl, tr)

let equate_tp tp tp' =
  let* env = read in
  let* res = lift_qu @@ Nbe.equal_tp tp tp' in
  if res then ret () else
    let* ttp = lift_qu @@ Nbe.quote_tp tp in
    let* ttp' = lift_qu @@ Nbe.quote_tp tp' in
    elab_err @@ Err.ExpectedEqualTypes (Env.pp_env env, ttp, ttp')


let with_pp k =
  let* env = read in
  k @@ Env.pp_env env

let expected_connective conn tp =
  with_pp @@ fun ppenv ->
  let* ttp = lift_qu @@ Nbe.quote_tp tp in
  elab_err @@ Err.ExpectedConnective (conn, ppenv, ttp)

let dest_pi =
  function
  | D.Pi (base, fam) ->
    ret (base, fam)
  | tp ->
    expected_connective `Pi tp

let dest_sg =
  function
  | D.Sg (base, fam) ->
    ret (base, fam)
  | tp ->
    expected_connective `Sg tp

let dest_id =
  function
  | D.Id (tp, l, r) ->
    ret (tp, l, r)
  | tp ->
    expected_connective `Id tp

let abstract nm tp k =
  push_var nm tp @@
  let* x = get_local 0 in
  k x

let abstract_dim nm k =
  push_var nm D.TpDim @@
  let* x = get_local 0 in
  k x

let define nm tp con k =
  push_def nm tp con @@
  let* x = get_local 0 in
  let* x = lift_cmp @@ Nbe.do_sub_out x in
  k x

let problem =
  let+ env = read in
  Env.problem env

let push_problem lbl =
  scope @@
  Env.push_problem lbl
