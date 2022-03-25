open CodeUnit

module D = Domain
module S = Syntax
module St = RefineState
module Env = RefineEnv
module Err = RefineError
module Sem = Semantics
module Qu = Quote
module Conv = Conversion

open Basis
include Monads.RefineM

open Monad.Notation (Monads.RefineM)

let refine_err err =
  let* env = read in
  Debug.print "Refiner failed, dumping environment...@;  %a" Env.dump env;
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

let throw_namespace_errors : ('a, 'error) Namespace.result -> 'a m =
  function
  | Result.Ok x -> ret x
  | Result.Error (`BindingNotFound path) -> refine_err @@ BindingNotFound (`User path)
  | Result.Error (`Shadowing path) -> refine_err @@ UnexpectedShadowing (`User path)

let with_ ~begin_ ~end_ m =
  let* st = get in
  let* a =
    trap @@
    let* () = begin_ st |>> set in
    let* m in
    let* st' = get in
    let* () = end_ ~parent:st ~child:st' |>> set in
    ret m
  in
  match a with
  | Ok a -> ret a
  | Error exn -> let* () = set st in throw exn

let add_global ~shadowing id tp con =
  let* st = get in
  let* sym, st' = throw_namespace_errors @@ St.add_global ~shadowing id tp con st in
  let+ () = set st' in
  sym

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

let get_lib = St.get_lib <@> get

let with_unit lib unit_id (action : 'a m) =
  with_
    ~begin_:(fun st -> ret @@ St.begin_unit lib unit_id st)
    ~end_:(fun ~parent ~child -> ret @@ St.end_unit ~parent ~child)
    action

let import ~shadowing pat unit_id =
  set @<< throw_namespace_errors @<< (St.import ~shadowing pat unit_id <@> get)

let loading_status id = St.loading_status id <@> get

let view ~shadowing pat =
  set @<< throw_namespace_errors @<< (St.transform_view ~shadowing pat <@> get)
let repack ~shadowing pat =
  set @<< throw_namespace_errors @<< (St.transform_export ~shadowing pat <@> get)
let export ~shadowing pat =
  set @<< throw_namespace_errors @<< (St.export_view ~shadowing pat <@> get)

let with_section ~shadowing ~prefix (action : 'a m) =
  with_
    ~begin_:(fun st -> ret @@ St.begin_section st)
    ~end_:(fun ~parent:_ ~child -> throw_namespace_errors @@ St.end_section ~shadowing ~prefix child)
    action

let eval con =
  lift_ev @@ Sem.eval con

let eval_tp tp =
  lift_ev @@ Sem.eval_tp tp

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

let update_span loc =
  scope @@ Env.set_location loc
