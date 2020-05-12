module CS = ConcreteSyntax
module D = Domain
module S = Syntax
module St = ElabState
module Env = ElabEnv
module Err = ElabError
module Qu = Quote
module Conv = Conversion

open CoolBasis
include Monads.ElabM

open Monad.Notation (Monads.ElabM)

let elab_err err =
  let* env = read in
  raise @@ Err.ElabError (err, Env.location env)

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

let get_global sym : (D.tp * D.con option) m =
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
  lift_qu @@ Conv.equal_con tp l r |>>
  function
  | `Ok -> ret ()
  | `Err err ->
    let* ttp = lift_qu @@ Qu.quote_tp tp in
    let* tl = lift_qu @@ Qu.quote_con tp l in
    let* tr = lift_qu @@ Qu.quote_con tp r in
    elab_err @@ Err.ExpectedEqual (Env.pp_env env, ttp, tl, tr, err)

let equate_tp tp tp' =
  let* env = read in
  lift_qu @@ Conv.equal_tp tp tp' |>>
  function
  | `Ok -> ret ()
  | `Err err ->
    let* ttp = lift_qu @@ Qu.quote_tp tp in
    let* ttp' = lift_qu @@ Qu.quote_tp tp' in
    elab_err @@ Err.ExpectedEqualTypes (Env.pp_env env, ttp, ttp', err)


let with_pp k =
  let* env = read in
  k @@ Env.pp_env env

let expected_connective conn tp =
  with_pp @@ fun ppenv ->
  let* ttp = lift_qu @@ Qu.quote_tp tp in
  elab_err @@ Err.ExpectedConnective (conn, ppenv, ttp)

let dest_pi =
  function
  | D.Pi (base, _, fam) ->
    ret (base, fam)
  | tp ->
    expected_connective `Pi tp

let dest_sg =
  function
  | D.Sg (base, _, fam) ->
    ret (base, fam)
  | tp ->
    expected_connective `Sg tp

let abstract nm tp k =
  let rho env =
    let con = D.mk_var tp @@ Env.size env in
    Env.append_con nm con tp env
  in
  scope rho @@
  k @<< get_local 0

let problem =
  let+ env = read in
  Env.problem env

let push_problem lbl =
  scope @@
  Env.push_problem lbl

let update_span loc =
  scope @@ Env.set_location loc
