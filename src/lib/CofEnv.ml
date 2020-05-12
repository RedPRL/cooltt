open CoolBasis

module D = Domain
module UF = DisjointSet.Make (PersistentTable.M)
module VarSet = Set.Make (Int)

type reduced_env =
  { classes : D.dim UF.t;
    (** equivalence classes of dimensions from reduced cofibrations *)

    true_vars : VarSet.t
  }

type env' =
  { classes : D.dim UF.t;
    (** equivalence classes of dimensions from reduced cofibrations *)

    true_vars : VarSet.t;
    (** set of cofibration variables assumed to be true *)

    unreduced_joins : D.cof list list;
    (** a stack of unreduced joins, each represented by a list of cofibrations *)
  }

type env = [ `Consistent of env' | `Inconsistent ]

let init () =
  `Consistent
    {classes = UF.init ~size:100;
     true_vars = VarSet.empty;
     unreduced_joins = []}

let inconsistent = `Inconsistent

let is_consistent =
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
    * [CoolBasis.Monad.Util.app] directly fit into this type. *)
  val seq : ('a -> t) -> 'a list -> t
end

module SearchHelper :
sig
  (** Pushes cofibrations into the environment.
      Invariant: input env.classes must be consistent.

      @return If the [env.classes] would be inconsistent, [None] is returned.
      Otherwise, [Some env] is returned and [env.classes] will be consistent. *)
  val pushes' : env' -> D.cof list -> env' option

  (** Checking whether the [env'] is inconsistent.
      Invariant: intput [env.classes] must be consistent;
      the inconsistency can only come from [env.unreduced_joins.] *)
  val consistency' : env' -> bool
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
          pushes' env (psis @ phis)
        | Cof.Join psis ->
          pushes' {env with unreduced_joins = psis :: unreduced_joins} phis
        | Cof.Eq (r, s) ->
          let classes = UF.union r s classes in
          if UF.find D.Dim0 classes = UF.find D.Dim1 classes then
            None
          else
            pushes' {env with classes} phis

  (** [consistency'] is almost a duplicate of the most general search. It exists because
    * (1) it's a clean way to avoid checking consistency within consistency and
    * (2) it's a clean way to avoid recursive modules. *)
  let rec consistency' ({classes; true_vars; unreduced_joins} as env) =
    match unreduced_joins with
    | [] -> true
    | psis :: unreduced_joins ->
      let search psi =
        Option.fold ~none:false ~some:consistency' @@ pushes' {env with unreduced_joins} [psi]
      in
      List.exists search psis
end

module Search : functor (M : SEQ) ->
sig
  (** Search all branches assuming more cofibrations. *)
  val left_invert : env -> D.cof list -> (reduced_env -> M.t) -> M.t

  (** Search all branches assuming more cofibrations.
      Invariant: [env.classes] must be consistent *)
  val left_invert' : env' -> D.cof list -> (reduced_env -> M.t) -> M.t
end =
functor (M : SEQ) ->
struct
  let left_invert' env phis cont =
    let rec go =
      function
      | None -> M.vacuous
      | Some ({classes; true_vars; unreduced_joins} as env) ->
        match unreduced_joins with
        | [] -> cont {classes; true_vars}
        | psis :: unreduced_joins ->
          if SearchHelper.consistency' env then
            let search psi =
              go (SearchHelper.pushes' {env with unreduced_joins} [psi])
            in
            M.seq search psis
          else
            M.vacuous
    in
    go (SearchHelper.pushes' env phis)

  let left_invert env phis cont =
    match env with
    | `Inconsistent -> M.vacuous
    | `Consistent env -> left_invert' env phis cont
end

(* Invariant: local.classes must be consistent. *)
let rec test (local : reduced_env) : D.cof -> bool =
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

module BoolSeqAll = struct type t = bool let vacuous = true let seq = List.for_all end
module BoolSearchAll = Search (BoolSeqAll)
let test_sequent env cx phi =
  BoolSearchAll.left_invert env cx @@
  fun env -> test env phi

let assume env phi =
  match env with
  | `Inconsistent -> env
  | `Consistent env ->
    match
      SearchHelper.pushes' env [Cof.reduce phi] (* do we want Cof.reduce here? *)
    with
    | None -> `Inconsistent
    | Some env ->
      if SearchHelper.consistency' env
      then `Consistent env
      else `Inconsistent

(** Monadic interface *)
module M (M : CoolBasis.Monad.S) :
sig
  (* Search all branches induced by unreduced joins under additional cofibrations. *)
  val left_invert_under_cofs : env -> D.cof list -> (env -> unit M.m) -> unit M.m
end
=
struct
  module MU = CoolBasis.Monad.Util (M)
  module Seq = struct type t = unit M.m let vacuous = M.ret () let seq = MU.iter end
  module S = Search (Seq)

  let left_invert_under_cofs env phis cont =
    S.left_invert env phis @@ fun {classes; true_vars} ->
    cont @@ `Consistent {classes; true_vars; unreduced_joins = []}
end
