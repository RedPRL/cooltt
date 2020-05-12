open CoolBasis

module D = Domain
module UF = DisjointSet.Make (PersistentTable.M)
module VarSet = Set.Make (Int)

type reduced_env =
  { classes : D.dim UF.t;
    (** equivalence classes of dimensions from reduced cofibrations *)

    true_vars : VarSet.t
  }

type consistent_env =
  { classes : D.dim UF.t;
    (** equivalence classes of dimensions from reduced cofibrations *)

    true_vars : VarSet.t;

    unreduced_joins : D.cof list list;
    (** a stack of unreduced joins, each represented by a list of cofibrations *)
  }

type env = [ `Consistent of consistent_env | `Inconsistent ]

let init () = `Consistent
    {classes = UF.init ~size:100;
     true_vars = VarSet.empty;
     unreduced_joins = []}

let inconsistent = `Inconsistent

let already_inconsistent =
  function
  | `Consistent _ -> `Consistent
  | `Inconsistent -> `Inconsistent

let find_class classes r =
  try UF.find r classes with _ -> r

module type SEQ =
sig
  type t
  val vacuous : t
  val seq : ('a -> t) -> 'a list -> t
end

module rec Search : functor (M : SEQ) ->
sig
  (* Search all branches assuming more cofibrations *)
  val left_inverse : env -> D.cof list -> (reduced_env -> M.t) -> M.t
  (* Search all branches assuming more cofibrations *)
  val left_inverse' : consistent_env -> D.cof list -> (reduced_env -> M.t) -> M.t
end
  =
  functor (M : SEQ) ->
  struct
    let left_inverse' env phis cont =
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
              if Test.simple env Cof.bot then M.vacuous else go env phis
            | Cof.Eq (r, s) ->
              let classes = UF.union r s classes in
              if UF.find D.Dim0 classes = UF.find D.Dim1 classes then
                M.vacuous
              else
                go {env with classes} phis
      in go env phis

    let left_inverse env phis cont =
      match env with
      | `Inconsistent -> M.vacuous
      | `Consistent env -> left_inverse' env phis cont
  end
and Test :
sig
  val simple : consistent_env -> D.cof -> bool
  val sequent : consistent_env -> D.cof list -> D.cof -> bool
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

  let sequent env cx phi = M.left_inverse' env cx (fun env -> right env phi)
  let simple env phi = sequent env [] phi
end

let test_sequent env cx phi =
  match env with
  | `Inconsistent -> true
  | `Consistent env -> Test.sequent env cx phi

let assume env phi =
  match env with
  | `Inconsistent -> env
  | `Consistent env ->
    let rec go env =
      function
      | [] -> `Consistent env
      | (phi :: phis) ->
        match phi with
        | Cof.Var v ->
          go {env with true_vars = VarSet.add v env.true_vars} phis
        | Cof.Cof phi ->
          match phi with
          | Cof.Meet psis ->
            go env (psis @ phis)
          | Cof.Join psis ->
            let env = {env with unreduced_joins = psis :: env.unreduced_joins} in
            if Test.simple env Cof.bot then `Inconsistent else go env phis
          | Cof.Eq (r, s) ->
            let classes = UF.union r s env.classes in
            if UF.find D.Dim0 classes = UF.find D.Dim1 classes then
              `Inconsistent
            else
              go {env with classes} phis
    in go env [Cof.reduce phi] (* do we want Cof.reduce here? *)

(** Monadic interface *)
module M (M : CoolBasis.Monad.S) :
sig
  (* Search all branches under one more cofibration *)
  val left_inverse_under_cofs : env -> D.cof list -> (env -> unit M.m) -> unit M.m
end
=
struct
  module MU = CoolBasis.Monad.Util (M)
  module Seq = struct type t = unit M.m let vacuous = M.ret () let seq = MU.app end
  module S = Search (Seq)

  let left_inverse_under_cofs env phis cont = S.left_inverse env phis @@
    fun {classes; true_vars} -> cont @@ `Consistent {classes; true_vars; unreduced_joins = []}
end
