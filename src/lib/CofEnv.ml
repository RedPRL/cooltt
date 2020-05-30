open CoolBasis

open Dim

type cof = (Dim.dim, int) Cof.cof

module UF = DisjointSet.Make (struct type t = dim let compare = compare end)
module VarSet = Set.Make (Int)

type reduced_env =
  { classes : UF.t;
    (** equivalence classes of dimensions from reduced cofibrations *)

    true_vars : VarSet.t
  }

type env' =
  { classes : UF.t;
    (** equivalence classes of dimensions from reduced cofibrations *)

    true_vars : VarSet.t;
    (** set of cofibration variables assumed to be true *)

    unreduced_joins : cof list list;
    (** a stack of unreduced joins, each represented by a list of cofibrations *)
  }

type env = [ `Consistent of env' | `Inconsistent ]

let init () =
  `Consistent
    {classes = UF.init;
     true_vars = VarSet.empty;
     unreduced_joins = []}

let inconsistent = `Inconsistent

let consistency =
  function
  | `Consistent _ -> `Consistent
  | `Inconsistent -> `Inconsistent

let find_class classes r =
  try UF.find r classes with _ -> r

(* minimum requirement to do the search *)
module type SEQ =
sig
  (** The type of the result of the search. *)
  type t

  (** The default value for vacuous cases. Should be the same as [seq id []]. *)
  val vacuous : t

  (** The sequencing operator. Technically, we can demand [seq' : t list -> t] instead
    * and the current [seq f l] would be [seq' (map f l)]. However, [List.for_all] and
    * [CoolBasis.Monad.Util.iter] directly fit into this type. *)
  val seq : ('a -> t) -> 'a list -> t

  (** If the first component returns a "good" result, then don't bother with the second. (???) *)
  val fast_track : (unit -> t) -> (unit -> t) -> t
end

module SearchHelper :
sig
  (** Pushes cofibrations into the environment.
      Invariant: input env.classes must be consistent.

      @return If the [env.classes] would be inconsistent, [None] is returned.
      Otherwise, [Some env] is returned and [env.classes] will be consistent. *)
  val pushes' : env' -> cof list -> env' option

  (** Checking whether the [env'] is consistent.
      Invariant: intput [env.classes] must be consistent;
      the inconsistency can only come from [env.unreduced_joins.] *)
  val is_consistent : env' -> bool
end
=
struct
  let rec pushes' ({classes; true_vars; unreduced_joins} as env) =
    function
    | [] -> Some env
    | phi :: phis ->
      match phi with
      | Cof.Var v ->
        pushes' {env with true_vars = VarSet.add v true_vars} phis
      | Cof.Cof phi ->
        match phi with
        | Cof.Meet psis ->
          pushes' env @@ psis @ phis
        | Cof.Join psis ->
          pushes' {env with unreduced_joins = psis :: unreduced_joins} phis
        | Cof.Eq (r, s) ->
          let classes = UF.union r s classes in
          if UF.find Dim0 classes = UF.find Dim1 classes then
            None
          else
            pushes' {env with classes} phis

  (** [is_consistent] is almost a duplicate of the most general search. It exists because
    * (1) it's a clean way to avoid checking consistency within consistency and
    * (2) it's a clean way to avoid recursive modules. *)
  let rec is_consistent ({classes; true_vars; unreduced_joins} as env) =
    match unreduced_joins with
    | [] -> true
    | psis :: unreduced_joins ->
      psis |> List.exists @@ fun psi ->
      Option.fold ~none:false ~some:is_consistent @@
      pushes' {env with unreduced_joins} [psi]
end

module Search (M : SEQ) :
sig
  (** Search all branches assuming more cofibrations. *)
  val left_invert : env -> cof list -> (reduced_env -> M.t) -> M.t

  (** Search all branches assuming more cofibrations.
      Invariant: [env.classes] must be consistent *)
  val left_invert' : env' -> cof list -> (reduced_env -> M.t) -> M.t
end =
struct
  let left_invert' env phis cont =
    let rec go =
      function
      | None -> M.vacuous
      | Some ({classes; true_vars; unreduced_joins} as env) ->
        M.fast_track (fun _ -> cont {classes; true_vars}) @@ fun _ ->
        match unreduced_joins with
        | [] -> cont {classes; true_vars}
        | psis :: unreduced_joins ->
          if SearchHelper.is_consistent env then
            psis |> M.seq @@ fun psi ->
            go @@ SearchHelper.pushes' {env with unreduced_joins} [psi]
          else
            M.vacuous
    in
    go @@ SearchHelper.pushes' env phis

  let left_invert env phis cont =
    match env with
    | `Inconsistent -> M.vacuous
    | `Consistent env -> left_invert' env phis cont
end


(* Invariant: local.classes must be consistent. *)
let rec test (local : reduced_env) : cof -> bool =
  function
  | Cof.Cof phi ->
    begin
      match phi with
      | Cof.Eq (r, s) when r = s ->
        true
      | Cof.Eq (r, s) ->
        find_class local.classes r = find_class local.classes s
      | Cof.Join phis ->
        List.exists (test local) phis
      | Cof.Meet phis ->
        List.for_all (test local) phis
    end
  | Cof.Var v ->
    VarSet.mem v local.true_vars

module BoolSeqAll : SEQ with type t = bool =
struct
  type t = bool
  let vacuous = true
  let seq = List.for_all
  let fast_track x y =
    if x () then true else y ()
end

module BoolSearchAll = Search (BoolSeqAll)

let test_sequent env cx phi =
  BoolSearchAll.left_invert env cx @@ fun env ->
  test env phi

let assume env phi =
  match env with
  | `Inconsistent -> env
  | `Consistent env ->
    match
      SearchHelper.pushes' env [Cof.reduce phi] (* do we want Cof.reduce here? *)
    with
    | None -> `Inconsistent
    | Some env ->
      if SearchHelper.is_consistent env
      then `Consistent env
      else `Inconsistent

(** Monadic interface *)
module M (M : CoolBasis.Monad.S) :
sig
  (** Search all branches induced by unreduced joins under additional cofibrations. *)
  val left_invert_under_cofs : env -> cof list -> (env -> unit M.m) -> unit M.m
end
=
struct
  module MU = CoolBasis.Monad.Util (M)
  module Seq = struct type t = unit M.m let vacuous = M.ret () let seq = MU.iter let fast_track _ x = x () end
  module S = Search (Seq)

  let left_invert_under_cofs env phis cont =
    S.left_invert env phis @@ fun {classes; true_vars} ->
    cont @@ `Consistent {classes; true_vars; unreduced_joins = []}
end
