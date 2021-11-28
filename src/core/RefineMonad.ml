open CodeUnit

module D = Domain
module S = Syntax
module St = RefineState
module Env = RefineEnv
module Err = RefineError
module Metadata = RefineMetadata
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
    match St.resolve_global (Env.current_unit_id env) id st with
    | Some sym -> ret @@ `Global sym
    | None -> ret `Unbound

let get_current_unit_id =
  let* env = read in
  ret @@ Env.current_unit_id env

let add_global id tp con =
  let* st = get in
  let* current_unit_id = get_current_unit_id in
  let sym, st' = St.add_global current_unit_id id tp con st in
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

let with_code_unit lib unit_id (action : 'a m) =
  let* () = modify (St.init_unit unit_id) in
  scope (fun _ -> Env.set_current_unit_id unit_id (Env.init lib)) action

let get_current_lib =
  let* env = read in
  ret @@ Env.current_lib env

let get_current_unit =
  let* st = get in
  let* current_unit_id = get_current_unit_id in
  ret @@ St.get_unit current_unit_id st

let add_import modifier code_unit =
  let* current_unit_id = get_current_unit_id in
  modify (St.add_import current_unit_id modifier code_unit)

let get_import path =
  let+ st = get in
  St.get_import path st

let is_imported path =
  let+ st = get in
  St.is_imported path st

let quote_con tp con =
  lift_qu @@ Qu.quote_con tp con

let quote_tp tp =
  lift_qu @@ Qu.quote_tp tp

let quote_sign sign =
  lift_qu @@ Qu.quote_sign sign

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

let expected_field sign con lbl =
  with_pp @@ fun ppenv ->
  let* tsign = quote_sign sign in
  refine_err @@ Err.ExpectedField (ppenv, tsign, con, lbl)

let field_names_mismatch ~expected ~actual =
  refine_err @@ Err.FieldNameMismatches (expected, actual)

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

let emit_tp loc tp =
  match loc with
  | Some loc ->
    let* env = read in
    let* qtp = quote_tp tp in
    modify (St.add_metadata (Metadata.TypeAt (loc, Env.pp_env env, qtp)))
  | None ->
    ret ()

let emit_hole ctx tp =
  let* env = read in
  match Env.location env with
  | Some loc -> 
    let hole = Metadata.Hole { ctx; tp } in
    modify (St.add_metadata (Metadata.HoleAt (loc, Env.pp_env env, hole)))
  | None -> ret ()
