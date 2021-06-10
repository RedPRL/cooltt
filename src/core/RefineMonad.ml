module D = Domain
module S = Syntax
module St = RefineState
module Env = RefineEnv
module Err = RefineError
module Qu = Quote
module Conv = Conversion

open Basis
include Monads.RefineM

open Monad.Notation (Monads.RefineM)

let refine_err err =
  let* env = read in
  throw @@ Err.RefineError (err, Env.location env)

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

let with_code_unit unit_name (action : unit -> 'a m) =
  let* st = get in
  let cunit = St.get_current_unit st in
  let st' = St.enter_unit unit_name st in
  let* _ = set st' in
  let* a = action () in
  let* _ = modify (St.restore_unit (CodeUnit.name cunit)) in
  ret a

let get_current_unit =
  let* st = get in
  ret @@ St.get_current_unit st

let add_import path code_unit =
  modify (St.add_import path code_unit)

let get_import path =
  let* st = get in
  ret @@ St.get_import path st

let quote_con tp con =
  lift_qu @@ Qu.quote_con tp con

let quote_tp tp =
  lift_qu @@ Qu.quote_tp tp

let quote_cut cut =
  lift_qu @@ Qu.quote_cut cut

let quote_cof cof =
  lift_qu @@ Qu.quote_cof cof

let quote_dim con =
  lift_qu @@ Qu.quote_dim con


(* This is extremely low-ch'i.
 * There should be a generic error-trapping function in src/basis/Monad. *)
let trap_conversion_err (m : unit m) : [`Ok | `Err of Conversion.Error.t] m =
  trap m |>> function
  | Error (Conversion.ConversionError err) -> ret @@ `Err err
  | Error exn -> throw exn
  | Ok _ -> ret `Ok


let equate tp l r =
  trap_conversion_err @@ lift_conv_ @@ Conv.equate_con tp l r |>>
  function
  | `Ok -> ret ()
  | `Err err ->
    let* env = read in
    let* ttp = quote_tp tp in
    let* tl = quote_con tp l in
    let* tr = quote_con tp r in
    refine_err @@ Err.ExpectedEqual (Env.pp_env env, ttp, tl, tr, err)

let equate_tp tp tp' =
  trap_conversion_err @@ lift_conv_ @@ Conv.equate_tp tp tp' |>>
  function
  | `Ok -> ret ()
  | `Err err ->
    let* env = read in
    let* ttp = quote_tp tp in
    let* ttp' = quote_tp tp' in
    refine_err @@ Err.ExpectedEqualTypes (Env.pp_env env, ttp, ttp', err)


let with_pp k =
  let* env = read in
  k @@ Env.pp_env env

let expected_connective conn tp =
  with_pp @@ fun ppenv ->
  let* ttp = quote_tp tp in
  refine_err @@ Err.ExpectedConnective (conn, ppenv, ttp)

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
