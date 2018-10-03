module D = Domain
module Syn = Syntax
type env_entry =
    Term of {term : D.t; tp : D.t; locks : int; is_active : bool}
  | TopLevel of {term : D.t; tp : D.t}
  | Tick of {locks : int; is_active : bool}
type env = env_entry list

let add_term ~term ~tp env = Term {term; tp; locks = 0; is_active = true} :: env
let add_tick env = Tick {locks = 0; is_active = true} :: env

type error =
    Cannot_synth_term of Syn.t
  | Using_killed_tick
  | Using_killed_variable
  | Using_locked_tick
  | Using_locked_variable
  | Using_non_tick
  | Using_non_term
  | Type_mismatch of D.t * D.t
  | Expecting_universe of D.t
  | Misc of string

let pp_error = function
  | Cannot_synth_term t -> "Cannot synthesize the type of:\n" ^ Syn.pp t
  | Using_killed_tick -> "Cannot use a tick after using a tick before it"
  | Using_killed_variable -> "Cannot use a variable after using a tick or stripping a lock before it"
  | Using_locked_tick -> "Cannot use a tick behind a lock"
  | Using_locked_variable -> "Cannot use a variable behind a lock"
  | Using_non_tick -> "Cannot use a normal term as a tick"
  | Using_non_term -> "Cannot use a tick as a term"
  | Type_mismatch (t1, t2) -> "Cannot equate\n" ^ D.pp t1 ^ " with\n" ^ D.pp t2
  | Expecting_universe d -> "Expected some universe but found\n" ^ D.pp d
  | Misc s -> s

exception Type_error of error

let tp_error e = raise (Type_error e)

let env_to_sem_env size =
  List.mapi
    (fun i -> function
       | TopLevel {term; _} -> term
       | Term {term; _} -> term
       | Tick _ -> Tick (size - (i + 1)))

module S = Set.Make(struct type t = int;; let compare = compare end)

let free_vars =
  let open Syntax in
  let rec go min = function
    | Var i -> if min <= i then S.singleton (i - min) else S.empty
    | Lam t | Next t | Later t -> go (min + 1) t
    | Let (t1, t2) | Pi (t1, t2) | Sig (t1, t2) | DFix (t1, t2) ->
      S.union (go min t1) (go (min + 1) t2)
    | Pair (t1, t2) | Check (t1, t2) | Ap (t1, t2) | Prev (t1, t2) -> S.union (go min t1) (go min t2)
    | Nat | Zero | Uni _ | Bullet -> S.empty
    | Fold (_, idx_tp, tp, idx, t, tick)
    | Unfold (_, idx_tp, tp, idx, t, tick) ->
      go min idx_tp
      |> S.union (go (min + 1) tp)
      |> S.union (go min idx)
      |> S.union (go min t)
      |> S.union (go min tick)
    | Suc t | Box t | Open t | Shut t | Fst t | Snd t -> go min t
    | NRec (m, zero, suc, n) ->
      go (min + 1) m
      |> S.union (go min zero)
      |> S.union (go (min + 2) suc)
      |> S.union (go min n) in
  go 0

let strip_env support =
  let rec delete_n_locks n = function
    | TopLevel r -> TopLevel r
    | Term r -> Term {r with locks = r.locks - n}
    | Tick r -> Tick {r with locks = r.locks - n} in
  let rec go i = function
    | [] -> []
    | TopLevel r :: env -> TopLevel r :: go (i + 1) env
    | Term {term; tp; is_active; locks} :: env ->
      if S.mem i support
      (* Cannot weaken this term! *)
      then Term {is_active; tp; term; locks = 0} :: List.map (delete_n_locks locks) env
      else Term {term; tp; is_active = false; locks = 0} :: go (i + 1) env
    | Tick {locks; is_active} :: env ->
      if S.mem i support
      (* Cannot weaken this tick! *)
      then Tick {locks = 0; is_active} :: List.map (delete_n_locks locks) env
      else Tick {locks = 0; is_active = false} :: go (i + 1) env in
  go 0

let use_tick env i =
  List.mapi
    (fun j -> function
       | TopLevel r -> TopLevel r
       | Term r -> Term {r with is_active = r.is_active && j > i}
       | Tick r -> Tick {r with is_active = r.is_active && j > i})
    env

let assert_tick env = function
  | Syn.Bullet -> ()
  | Syn.Var i ->
    begin
      match List.nth env i with
      | Tick _ -> ()
      | _ -> tp_error Using_non_tick
    end
  | _ -> tp_error Using_non_tick

let apply_lock =
  List.map
    (function
      | TopLevel r -> TopLevel r
      | Tick t -> Tick {t with locks = t.locks + 1}
      | Term t -> Term {t with locks = t.locks + 1})

let get_var env n = match List.nth env n with
  | Term {term = _; tp; locks = 0; is_active = true} -> tp
  | Term {is_active = false; _} -> tp_error Using_killed_variable
  | TopLevel {tp; _} -> tp
  | Term _ -> tp_error Using_locked_variable
  | Tick _  -> tp_error Using_non_term

let get_tick env n = match List.nth env n with
  | Tick {locks = 0; is_active = true} -> ()
  | Tick {is_active = false; _} -> tp_error Using_killed_tick
  | Tick _ -> tp_error Using_locked_tick
  | TopLevel _ -> tp_error Using_non_tick
  | Term _ -> tp_error Using_non_tick

let assert_subtype size t1 t2 =
  if Nbe.check_subtype size t1 t2
  then ()
  else tp_error (Type_mismatch (t1, t2))

let rec check ~env ~size ~term ~tp =
  match term with
  | Syn.Let (def, body) ->
    let def_tp = synth ~env ~size ~term:def in
    let def_val = Nbe.eval def (env_to_sem_env size env) in
    check ~env:(add_term ~term:def_val ~tp:def_tp env) ~size:(size + 1) ~term:body ~tp
  | Nat ->
    begin
      match tp with
      | D.Uni _ -> ()
      | t -> tp_error (Expecting_universe t)
    end
  | Pi (l, r) | Sig (l, r) ->
    check ~env ~size ~term:l ~tp;
    let l_sem = Nbe.eval l (env_to_sem_env size env) in
    let var = D.mk_var l_sem size in
    check ~env:(add_term ~term:var ~tp:l_sem env) ~size ~term:r ~tp
  | Lam body ->
    begin
      match tp with
      | D.Pi (arg_tp, clos) ->
        let var = D.mk_var arg_tp size in
        let dest_tp = Nbe.do_clos clos var in
        check ~env:(add_term ~term:var ~tp:arg_tp env) ~size:(size + 1) ~term:body ~tp:dest_tp;
      | t -> tp_error (Misc ("Expecting Pi but found\n" ^ D.pp t))
    end
  | Pair (left, right) ->
    begin
      match tp with
      | D.Sig (left_tp, right_tp) ->
        check ~env ~size ~term:left ~tp:left_tp;
        let left_sem = Nbe.eval left (env_to_sem_env size env) in
        check ~env ~size ~term:right ~tp:(Nbe.do_clos right_tp left_sem)
      | t -> tp_error (Misc ("Expecting Sig but found\n" ^ D.pp t))
    end
  | Later t -> check ~env:(add_tick env) ~size:(size + 1) ~term:t ~tp
  | Next t ->
    begin
      match tp with
      | Later clos ->
        let tp = Nbe.do_tick_clos clos (Tick size) in
        check ~env:(add_tick env) ~size:(size + 1) ~term:t ~tp
      | t -> tp_error (Misc ("Expecting Later but found\n" ^ D.pp t))
    end
  | Box term -> check ~env:(apply_lock env) ~size ~term ~tp
  | Shut term ->
    begin
      match tp with
      | Box tp -> check ~env:(apply_lock env) ~size ~term ~tp
      | t -> tp_error (Misc ("Expecting Box but found\n" ^ D.pp t))
    end
  | Uni i ->
    begin
      match tp with
      | Uni j when i < j -> ()
      | t ->
        let msg =
          "Expecting universe over " ^ string_of_int i ^ " but found\n" ^ D.pp t in
        tp_error (Misc msg)
    end
  | Bullet -> tp_error Using_non_term
  | term -> assert_subtype size (synth ~env ~size ~term) tp

and synth ~env ~size ~term =
  match term with
  | Syn.Var i -> get_var env i
  | Check (term, tp') ->
    let tp = Nbe.eval tp' (env_to_sem_env size env) in
    check ~env ~size ~term ~tp;
    tp
  | Zero -> D.Nat
  | Suc term -> check ~env ~size ~term ~tp:Nat; D.Nat
  | Fst p ->
    begin
      match synth ~env ~size ~term:p with
      | Sig (left_tp, _) -> left_tp
      | t -> tp_error (Misc ("Expecting Sig but found\n" ^ D.pp t))
    end
  | Snd p ->
    begin
      match synth ~env ~size ~term:p with
      | Sig (_, right_tp) ->
        let proj = Nbe.eval (Fst p) (env_to_sem_env size env) in
        Nbe.do_clos right_tp proj
      | t -> tp_error (Misc ("Expecting Sig but found\n" ^ D.pp t))
    end
  | Ap (f, a) ->
    begin
      match synth ~env ~size ~term:f with
      | Pi (src, dest) ->
        check ~env ~size ~term:a ~tp:src;
        let a_sem = Nbe.eval a (env_to_sem_env size env) in
        Nbe.do_clos dest a_sem
      | t -> tp_error (Misc ("Expecting Pi but found\n" ^ D.pp t))
    end
  | Prev (term, tick) ->
    begin
      match tick with
      | Var i ->
        get_tick env i;
        let i' = size - (i + 1) in
        begin
          match synth ~env:(use_tick env i) ~size ~term with
          | Later clos -> Nbe.do_tick_clos clos (Tick i')
          | t -> tp_error (Misc ("Expecting Later but found\n" ^ D.pp t))
        end
      | Bullet ->
        begin
          match synth ~env:(apply_lock env) ~size ~term with
          | Later clos -> Nbe.do_tick_clos clos Bullet
          | t -> tp_error (Misc ("Expecting Later but found\n" ^ D.pp t))
        end
      | _ -> tp_error Using_non_tick
    end
  | NRec (mot, zero, suc, n) ->
    check ~env ~size ~term:n ~tp:Nat;
    let var = D.mk_var Nat size in
    check_tp ~env:(add_term ~term:var ~tp:Nat env) ~size:(size + 1) ~term:mot;
    let sem_env = env_to_sem_env size env in
    let zero_tp = Nbe.eval mot (Zero :: sem_env) in
    let ih_tp = Nbe.eval mot (var :: sem_env) in
    let ih_var = D.mk_var ih_tp (size + 1) in
    let suc_tp = Nbe.eval mot (Suc var :: sem_env) in
    check ~env ~size ~term:zero ~tp:zero_tp;
    check
      ~env:(add_term ~term:var ~tp:Nat env |> add_term ~term:ih_var ~tp:ih_tp)
      ~size:(size + 2)
      ~term:suc
      ~tp:suc_tp;
    Nbe.eval mot (Nbe.eval n sem_env :: sem_env)
  | Open term ->
    let support = free_vars term in
    let env = strip_env support env in
    begin
      match synth ~env ~size ~term with
      | Box tp -> tp
      | t -> tp_error (Misc ("Expecting Box but found\n" ^ D.pp t))
    end
  | DFix (tp', body) ->
    let tp'_sem = Nbe.eval tp' (env_to_sem_env size env) in
    let later_tp'_sem = D.Later (ConstTickClos tp'_sem) in
    let var = D.mk_var later_tp'_sem size in
    check ~env:(add_term ~term:var ~tp:later_tp'_sem env) ~size:(size + 1) ~term:body ~tp:tp'_sem;
    later_tp'_sem
  | Fold (uni, idx_tp, tp, idx, t, tick) ->
    synth_fold_unfold env size ~is_fold:true uni idx_tp tp idx t tick
  | Unfold (uni, idx_tp, tp, idx, t, tick) ->
    synth_fold_unfold env size ~is_fold:false uni idx_tp tp idx t tick
  | _ -> tp_error (Cannot_synth_term term)

and synth_fold_unfold env size ~is_fold uni idx_tp tp idx t tick =
  assert_tick env tick;
  let sem_env = env_to_sem_env size env in
  let idx_tp_sem = Nbe.eval idx_tp sem_env in
  let fix_idx_tp = D.Pi (idx_tp_sem, D.ConstClos (D.Uni uni)) in
  let later_fix_idx_tp = D.Later (D.ConstTickClos fix_idx_tp) in
  let fix_var = D.mk_var later_fix_idx_tp size in
  check
    ~env:(add_term ~term:fix_var ~tp:later_fix_idx_tp env)
    ~size:(size + 1)
    ~term:tp
    ~tp:fix_idx_tp;
  check ~env ~size ~term:idx ~tp:idx_tp_sem;
  let tp_sem = D.Clos {term = tp; env = sem_env} in
  let idx_sem = Nbe.eval idx sem_env in
  let tick_sem = Nbe.eval tick sem_env in
  let dfix_sem = D.DFix (fix_idx_tp, tp_sem) in
  (* God in heaven *)
  let unfolded_sem = Nbe.do_ap (Nbe.do_clos tp_sem dfix_sem) idx_sem in
  let folded_sem = Nbe.do_ap (Nbe.do_prev dfix_sem tick_sem) idx_sem in
  if is_fold
  then (check ~env ~size ~term:t ~tp:unfolded_sem; folded_sem)
  else (check ~env ~size ~term:t ~tp:folded_sem; unfolded_sem)

and check_tp ~env ~size ~term =
  match term with
  | Syn.Nat -> ()
  | Uni _ -> ()
  | Box term -> check_tp ~env:(apply_lock env) ~size ~term
  | Later term -> check_tp ~env:(add_tick env) ~size:(size + 1) ~term
  | Pi (l, r) | Sig (l, r) ->
    check_tp ~env ~size ~term:l;
    let l_sem = Nbe.eval l (env_to_sem_env size env) in
    let var = D.mk_var l_sem size in
    check_tp ~env:(add_term ~term:var ~tp:l_sem env) ~size:(size + 1) ~term:r
  | Let (def, body) ->
    let def_tp = synth ~env ~size ~term:def in
    let def_val = Nbe.eval def (env_to_sem_env size env) in
    check_tp ~env:(add_term ~term:def_val ~tp:def_tp env) ~size:(size + 1) ~term:body
  | term ->
    begin
      match synth ~env ~size ~term with
      | D.Uni _ -> ()
      | t -> tp_error (Expecting_universe t)
    end
