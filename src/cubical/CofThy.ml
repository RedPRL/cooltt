open Basis
open Bwd
open Dim

module ConsistencyMonad =
struct
  type 'a m = [ `Consistent of 'a | `Inconsistent ]
  let ret x : 'a m = `Consistent x
  let keep_consistent (f : 'a -> 'b m) (l : 'a list) : 'b list =
    List.filter_map (fun x -> match f x with `Inconsistent -> None | `Consistent y -> Some y) l
  let bind m f =
    match m with
    | `Inconsistent -> `Inconsistent
    | `Consistent x -> f x
end
module ConsistencyMonadUtil = Monad.Util(ConsistencyMonad)
open Monad.Notation(ConsistencyMonad)

module CofVar =
struct
  type t = [`L of int | `G of Symbol.t]
  let compare = compare
end

type cof = (Dim.dim, CofVar.t) Cof.cof

module UF = DisjointSet.Make (struct type t = dim let compare = compare end)
module Assignment =
struct
  module VarMap = Map.Make (CofVar)
  type t = bool VarMap.t

  let empty : t = VarMap.empty

  let is_empty : t -> bool = VarMap.is_empty

  (* Unsafe variants : assuming no conflicts *)
  let add v b (m : t) =
    match VarMap.find_opt v m with
    | None -> `Consistent (VarMap.add v b m)
    | Some b' -> if b = b' then `Consistent m else `Inconsistent
  let unsafe_add v b (m : t) = VarMap.add v b m

  let union (m1 : t) (m2 : t) =
    let exception Conflict in
    let merger _ b1 b2 = if b1 = b2 then Some b1 else raise Conflict in
    try `Consistent (VarMap.union merger m1 m2)
    with Conflict -> `Inconsistent
  let unsafe_union (m1 : t) (m2 : t) =
    let use_first _ b _ = Some b in VarMap.union use_first m1 m2

  let inter (m1 : t) (m2 : t) =
    let merger _ b1 b2 =
      match b1, b2 with
      | Some b1, Some b2 when b1 = b2 -> Some b1
      | _ -> None
    in
    VarMap.merge merger m1 m2

  let diff (m1 : t) (m2 : t) =
    let merger _ b1 b2 =
      match b1, b2 with
      | Some b1, Some b2 when b1 = b2 -> None
      | _ -> b1
    in
    VarMap.merge merger m1 m2

  let unsafe_rebase ~base (m : t) =
    let merger _ base_b b =
      match base_b, b with
      | Some _, Some _ -> None
      | _ -> b
    in
    VarMap.merge merger base m

  let of_list l : t ConsistencyMonad.m =
    List.fold_left (fun ass (v, b) -> ass |>> add v b) (`Consistent empty) l

  let test v b (m : t) =
    try VarMap.find v m = b with Not_found -> false

  (* Not sure if it's faster to use [VarMap.for_all] and [test].
     The asymptotic analysis would prefer the current code but
     the numbers of cofibration variables are very small in practice. *)
  let subset (m1 : t) m2 =
    let exception Failure in
    let merger _ b1 b2 =
      match b1, b2 with
      | None, _ -> None
      | Some b1, Some b2 when b1 = b2 -> None
      | _ -> raise Failure
    in
    try ignore (VarMap.merge merger m1 m2); true
    with Failure -> false
end

(** A presentation of an algebraic theory over the language of intervals and cofibrations. *)
type alg_thy' =
  { classes : UF.t;
    (** equivalence classes of dimensions *)

    known_vars : Assignment.t
  }

type var = CofVar.t * bool
type eq = Dim.dim * Dim.dim
let neg_eq r1 r2 = Cof.neg_eq ~dim0:Dim0 ~dim1:Dim1 r1 r2

(** A [branch] represents the meet of a bunch of atomic cofibrations. *)
type branch = var list * eq list
type branches = branch list

(** A [cached_branch] is a [branch] together with an algebraic theory
  * representing the resulting theory at the end of the branch.  *)
type cached_branch = alg_thy' * (Assignment.t * eq list)
type cached_branches = cached_branch list

(** As an optimization, we remember when a theory is consistent or not. *)
type alg_thy = alg_thy' ConsistencyMonad.m

(** A disjoint theory is the join of a list of [cached_branch]. We do not need to
  * remember the common ancestor of these branches (as an algebraic theory), but only
  * the atomic cofibrations labeling the path from the common ancestor to each branch. *)
type disj_thy = cached_branches

(** This is to dissect the meet of a list of cofibrations into a list of branches.
  *
  * Possible further optimizations:
  * 1. Should we use [Cof.reduce] to massage the cofibrations first?
  * 2. Should we eagerly factor out common cofibrations to facilitate the refactoring
  *    steps later on? (This does not seem to be helpful in preliminary experiments.)
*)
let rec dissect_cofibrations : cof list -> branches =
  function
  | [] -> [[], []]
  | cof :: cofs ->
    match cof with
    | Cof.Var v ->
      List.map (fun (vars, eqs) -> (v, true) :: vars, eqs) @@
      dissect_cofibrations cofs
    | Cof.Cof cof ->
      match cof with
      | Cof.Meet meet_cofs ->
        dissect_cofibrations @@ meet_cofs @ cofs
      | Cof.Join join_cofs ->
        join_cofs |> List.concat_map @@ fun join_cof ->
        dissect_cofibrations @@ join_cof :: cofs
      | Cof.Eq (r, s) ->
        List.map (fun (vars, eqs) -> vars, (r, s) :: eqs) @@
        dissect_cofibrations cofs
      | Cof.Neg cof ->
        match cof with
        | Cof.Var v ->
          List.map (fun (vars, eqs) -> (v, false) :: vars, eqs) @@
          dissect_cofibrations cofs
        | Cof.Cof cof ->
          match cof with
          | Cof.Meet negated_meet_cofs ->
            negated_meet_cofs |> List.concat_map @@ fun negated_meet_cof ->
            dissect_cofibrations @@ Cof.neg negated_meet_cof :: cofs
          | Cof.Join negated_join_cofs ->
            dissect_cofibrations @@ List.map Cof.neg negated_join_cofs @ cofs
          | Cof.Eq (r, s) ->
            dissect_cofibrations @@ neg_eq r s :: cofs
          | Cof.Neg cof ->
            dissect_cofibrations @@ cof :: cofs

module Alg =
struct
  type t = alg_thy
  type t' = alg_thy'

  let emp' =
    {classes = UF.empty;
     known_vars = Assignment.empty}

  let empty =
    `Consistent emp'

  let consistency =
    function
    | `Consistent _ -> `Consistent
    | `Inconsistent -> `Inconsistent

  let assume_vars (thy : t') vars =
    let+ known_vars = Assignment.union thy.known_vars vars in
    {thy with known_vars}

  let test_eq (thy : t') (r, s) =
    UF.test r s thy.classes

  (** [unsafe_test_and_assume_eq] fuses [test_eq] and [assume_eq] (if there was one).
    * It is "unsafe" because we do not check consistency here. *)
  let unsafe_test_and_assume_eq (thy : t') (r, s) =
    let testing, classes = UF.test_and_union r s thy.classes in
    testing, {thy with classes}

  let test_eqs (thy : t') eqs =
    List.for_all (test_eq thy) eqs

  let test_var (thy : t') v (b : bool) =
    Assignment.test v b thy.known_vars

  let test_vars (thy : t') vs =
    Assignment.subset vs thy.known_vars

  let test_branch (thy : t') (vars, eqs) =
    test_vars thy vars && test_eqs thy eqs

  (** [reduced_vars] takes out redundant cofibration variables. *)
  let reduce_vars (thy : t') vars =
    let+ thy' = assume_vars thy vars in
    let vars' = Assignment.unsafe_rebase ~base:thy.known_vars vars in
    (thy', vars')

  (** [reduce_eqs] detects inconsistency of an equation set and takes out
    * redundant equations. *)
  let reduce_eqs (thy : t') eqs =
    let go ((thy', eqs) as acc) eq =
      match unsafe_test_and_assume_eq thy' eq with
      | true, _ -> acc
      | false, thy' -> thy',  Snoc (eqs, eq)
    in
    let thy', eqs = List.fold_left go (thy, Emp) eqs in
    match test_eq thy' (Dim0, Dim1) with
    | true -> `Inconsistent
    | false -> `Consistent (thy', Bwd.to_list eqs)

  (** [reduce_branch] detects inconsistency of a branch and takes out redundant
    * cofibration variables and equations. *)
  let reduce_branch (thy : t') (vars, eqs) =
    let* vars = Assignment.of_list vars in
    let* thy, vars = reduce_vars thy vars in
    let+ thy, eqs = reduce_eqs thy eqs in
    (thy, (vars, eqs))

  (** [reduce_branches] removes inconsistent branches and takes out redundant
    * cofibration variables and equations. *)
  let reduce_branches (thy' : t') branches : cached_branches =
    ConsistencyMonad.keep_consistent (reduce_branch thy') branches

  (** [drop_useless_branches] drops the branches that could be dropped without
    * affecting the coverages. *)
  let drop_useless_branches cached_branches : cached_branches =
    let go_fwd acc (thy', branch) =
      if Bwd.exists (fun (_, branch) -> test_branch thy' branch) acc then
        acc
      else
        Snoc (acc, (thy', branch))
    in
    let cached_branches = List.fold_left go_fwd Emp cached_branches in
    let go_bwd (thy', branch) acc =
      if List.exists (fun (_, branch) -> test_branch thy' branch) acc then
        acc
      else
        (thy', branch) :: acc
    in
    Bwd.fold_right go_bwd cached_branches []

  (** [split] combines all the optimizers above to split an algebraic theory
    * into multiple ones induced by the input cofibration context. *)
  let split (thy : t) (cofs : cof list) : t list =
    match thy with
    | `Inconsistent -> []
    | `Consistent thy' ->
      match dissect_cofibrations cofs with
      | [] -> []
      | [[], []] -> [`Consistent thy']
      | dissected_cofs ->
        begin
          drop_useless_branches @@
          reduce_branches thy' dissected_cofs
        end |> List.map @@ fun (thy', _) -> `Consistent thy'

  (** [test] checks whether a cofibration is true within an algebraic theory. *)
  let rec test (thy' : alg_thy') : cof -> bool =
    function
    | Cof.Var v ->
      test_var thy' v true
    | Cof.Cof phi ->
      match phi with
      | Cof.Eq (r, s) ->
        test_eq thy' (r, s)
      | Cof.Join phis ->
        List.exists (test thy') phis
      | Cof.Meet phis ->
        List.for_all (test thy') phis
      | Cof.Neg cof ->
        test_neg thy' cof
  and test_neg (thy' : alg_thy') : cof -> bool =
    function
    | Cof.Var v ->
      test_var thy' v false
    | Cof.Cof phi ->
      match phi with
      | Cof.Eq (r, s) ->
        test thy' (neg_eq r s)
      | Cof.Join phis ->
        List.for_all (test_neg thy') phis
      | Cof.Meet phis ->
        List.exists (test_neg thy') phis
      | Cof.Neg cof ->
        test thy' cof

  let left_invert_under_cofs ~zero ~seq (thy : t) cofs cont =
    match split thy cofs with
    | [] -> zero
    | [thy] -> cont thy
    | thys -> seq cont thys
end

module Disj =
struct
  type t = disj_thy

  let envelop_alg' alg_thy' : disj_thy =
    [alg_thy', (Assignment.empty, [])]

  let envelope_alg =
    function
    | `Consistent alg_thy' -> envelop_alg' alg_thy'
    | `Inconsistent -> []


  let empty : t = [Alg.emp', (Assignment.empty, [])]

  let consistency =
    function
    | [] -> `Inconsistent
    | _ -> `Consistent

  (** [refactor_branches] attempts to identify common parts of the branches
    * and shrink the labels. Recall that we do not keep the common ancestor
    * but the paths (as a collection of atomic cofibrations) from the common
    * ancestor, and thus what are changed here are the paths.
    *
    * This optimization seems to be expensive, but it seems to help after
    * we switched from the persistant tables (using [Hashtbl]) to [Map].
  *)
  let refactor_branches cached_branches : t =
    let common_vars =
      let go vars0 (_, (vars1, _)) = Assignment.inter vars0 vars1 in
      match cached_branches with
      | [] -> Assignment.empty
      | (_, (vars, _)) :: branches -> List.fold_left go vars branches
    in
    (* The following is an approximation of checking whether some equation is useful.
     * It does not kill every "useless" cofibration. Here is one example:
     *
     * branch 1: r=0
     * branch 2: r=i, i=0
     *
     * r=0 will be factored out, but then i=0 should also be removed. Here is a more
     * complicated example:
     *
     * branch 1: r=i, i=0
     * branch 2: r=j, j=0
     *
     * Both i=0 and j=0 should be factored out, but the following code is not smart
     * enough to detect them. One could consider more aggressive approaches if [CofThy]
     * becomes the bottleneck again.
    *)
    let useful eq = cached_branches |> List.exists @@ fun (thy', _) -> not @@ Alg.test_eq thy' eq in
    (* revisit all branches and remove all useless ones identified by the simple criterion above. *)
    cached_branches |> List.map @@ fun (thy', (vars, eqs)) ->
    thy', (Assignment.diff vars common_vars, List.filter useful eqs)

  (** [split thy cofs] adds to the theory [thy] the conjunction of a list of cofibrations [cofs]
    * and calculate the branches accordingly. This is similar to [Alg.split] in the spirit but
    * differs in detail. *)
  let split (thy : t) (cofs : cof list) : t =
    match dissect_cofibrations cofs with
    | [] -> []
    | [[], []] -> thy
    | dissected_cofs ->
      Alg.drop_useless_branches begin
        thy |> List.concat_map @@ fun (thy', (vars, eq)) ->
        Alg.reduce_branches thy' dissected_cofs |> List.map @@ fun (thy', (sub_vars, sub_eqs)) ->
        thy', (Assignment.unsafe_union vars sub_vars, eq @ sub_eqs)
      end

  (** [assume thy cofs] is the same as [split thy cofs] except that it further refactors the
    * branches to optimize future searching. *)
  let assume (thy : t) (cofs : cof list) : t =
    refactor_branches @@ split thy cofs

  let test_sequent thy cx cof =
    begin
      split thy cx |> List.map (fun (thy', _) -> thy')
    end |> List.for_all @@ fun thy' -> Alg.test thy' cof

  let left_invert ~zero ~seq thy cont =
    match thy |> List.map @@ fun (thy', _) -> `Consistent thy' with
    | [] -> zero
    | [thy'] -> cont thy'
    | thy's -> seq cont thy's
end
