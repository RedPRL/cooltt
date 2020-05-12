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

    unreduced_joins : D.cof list list;
    (** a stack of unreduced joins, each represented by a list of cofibrations *)
  }

type env = [ `Consistent of env' | `Inconsistent ]

let init () = `Consistent
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
  (* The type of the result of the search. *)
  type t

  (* The default value for vacuous cases. Should be the same as `seq id []`. *)
  val vacuous : t

  (* The sequencing operator. Technically, we can demand `seq' : t list -> t` instead
   * and the current `seq f l` would be `seq' (map f l)`. However, `List.for_all` and
   * `CoolBasis.Monad.Util.app` directly fit into this type. *)
  val seq : ('a -> t) -> 'a list -> t
end

module rec Search : functor (M : SEQ) ->
sig
  (* Search all branches assuming more cofibrations *)
  val left_invert : env -> D.cof list -> (reduced_env -> M.t) -> M.t

  (* Search all branches assuming more cofibrations *)
  val left_invert' : env' -> D.cof list -> (reduced_env -> M.t) -> M.t
end
  =
  functor (M : SEQ) ->
  struct
    let left_invert' env phis cont =
      let rec go ({classes; true_vars; unreduced_joins} as env) =
        function
        | [] ->
          begin
            match unreduced_joins with
            | [] -> cont {classes; true_vars}
            | (psis :: unreduced_joins) ->
              M.seq (fun psi -> go {env with unreduced_joins} [psi]) psis
          end
        | (phi :: phis) ->
          match phi with
          | Cof.Var v ->
            go {env with true_vars = VarSet.add v true_vars} phis
          | Cof.Cof phi ->
            match phi with
            | Cof.Meet psis ->
              go env (psis @ phis)
            | Cof.Join psis ->
              let env = {env with unreduced_joins = psis :: unreduced_joins} in
              if Test.inconsistency env then M.vacuous else go env phis
            | Cof.Eq (r, s) ->
              let classes = UF.union r s classes in
              if UF.find D.Dim0 classes = UF.find D.Dim1 classes then
                M.vacuous
              else
                go {env with classes} phis
      in go env phis

    let left_invert env phis cont =
      match env with
      | `Inconsistent -> M.vacuous
      | `Consistent env -> left_invert' env phis cont
  end
and Test :
sig
  val inconsistency : env' -> bool
  val sequent : env' -> D.cof list -> D.cof -> bool
end =
struct
  (* Invariant: classes is consistent *)
  let rec right (local : reduced_env) =
    function
    | Cof.Cof phi ->
      begin
        match phi with
        | Cof.Eq (r, s) when r = s ->
          true
        | Cof.Eq (r, s) ->
          find_class local.classes r = find_class local.classes s
        | Cof.Join phis -> List.exists (right local) phis
        | Cof.Meet phis -> List.for_all (right local) phis
      end
    | Cof.Var v ->
      VarSet.mem v local.true_vars

  module Seq = struct type t = bool let vacuous = true let seq = List.for_all end
  module M = Search (Seq)

  let sequent env cx phi = M.left_invert' env cx (fun env -> right env phi)
  let inconsistency env = M.left_invert' env [] (fun _ -> false)
end

let test_sequent env cx phi =
  match env with
  | `Inconsistent -> true
  | `Consistent env -> Test.sequent env cx phi

let assume env phi =
  match env with
  | `Inconsistent -> env
  | `Consistent env ->
    let rec go ({classes; true_vars; unreduced_joins} as env) =
      function
      | [] -> if Test.inconsistency env then `Inconsistent else `Consistent env
      | (phi :: phis) ->
        match phi with
        | Cof.Var v ->
          go {env with true_vars = VarSet.add v true_vars} phis
        | Cof.Cof phi ->
          match phi with
          | Cof.Meet psis ->
            go env (psis @ phis)
          | Cof.Join psis ->
            go {env with unreduced_joins = psis :: unreduced_joins} phis
          | Cof.Eq (r, s) ->
            let classes = UF.union r s classes in
            if UF.find D.Dim0 classes = UF.find D.Dim1 classes then
              `Inconsistent
            else
              go {env with classes} phis
    in go env [Cof.reduce phi] (* do we want Cof.reduce here? *)

(** Monadic interface *)
module M (M : CoolBasis.Monad.S) :
sig
  (* Search all branches induced by unreduced joins under additional cofibrations. *)
  val left_invert_under_cofs : env -> D.cof list -> (env -> unit M.m) -> unit M.m
end
=
struct
  module MU = CoolBasis.Monad.Util (M)
  module Seq = struct type t = unit M.m let vacuous = M.ret () let seq = MU.app end
  module S = Search (Seq)

  let left_invert_under_cofs env phis cont =
    S.left_invert env phis @@ fun {classes; true_vars} ->
    cont @@ `Consistent {classes; true_vars; unreduced_joins = []}
end
