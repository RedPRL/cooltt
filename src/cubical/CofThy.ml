open ContainersLabels
open Basis
open Bwd

type cof = CofThyData.cof

module UF = DisjointSet.Make (Dim)
module VarSet = Set.Make (struct type t = CofThyData.var let compare = compare end)

(** A presentation of an algebraic theory over the language of intervals and cofibrations. *)
type alg_thy' =
  { classes : UF.t;
    (** equivalence classes of dimensions *)

    true_vars : VarSet.t
  }

type eq = Dim.t * Dim.t

(** A [branch] represents the meet of a bunch of atomic cofibrations. *)
type branch = VarSet.t * eq list
type branches = branch list

(** A [cached_branch] is a [branch] together with an algebraic theory
  * representing the resulting theory at the end of the branch.  *)
type cached_branch = alg_thy' * branch
type cached_branches = cached_branch list

(** As an optimization, we remember whether a theory is consistent or not. *)
type alg_thy = [ `Consistent of alg_thy' | `Inconsistent ]

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
  | [] -> [VarSet.empty, []]
  | cof :: cofs ->
    match cof with
    | Cof.Var v ->
      List.map (dissect_cofibrations cofs)
        ~f:(fun (vars, eqs) -> VarSet.add v vars, eqs)
    | Cof.Cof cof ->
      match cof with
      | Cof.Meet meet_cofs ->
        dissect_cofibrations @@ meet_cofs @ cofs
      | Cof.Join join_cofs ->
        List.concat_map join_cofs
          ~f:(fun join_cof -> dissect_cofibrations @@ join_cof :: cofs)
      | Cof.Eq (r, s) ->
        List.map (dissect_cofibrations cofs)
          ~f:(fun (vars, eqs) -> vars, (r, s) :: eqs)

module Alg =
struct
  type t = alg_thy
  type t' = alg_thy'

  let emp' =
    {classes = UF.empty;
     true_vars = VarSet.empty}

  let empty =
    `Consistent emp'

  let consistency =
    function
    | `Consistent _ -> `Consistent
    | `Inconsistent -> `Inconsistent

  let assume_vars (thy : t') vars =
    {thy with true_vars = VarSet.union vars thy.true_vars}

  let test_eq (thy : t') (r, s) =
    UF.test r s thy.classes

  (** [unsafe_test_and_assume_eq] fuses [test_eq] and [assume_eq] (if there was one).
    * It is "unsafe" because we do not check consistency here. *)
  let unsafe_test_and_assume_eq (thy : t') (r, s) =
    let testing, classes = UF.test_and_union r s thy.classes in
    testing, {thy with classes}

  let test_eqs (thy : t') eqs =
    List.for_all ~f:(test_eq thy) eqs

  let test_var (thy : t') v =
    VarSet.mem v thy.true_vars

  let test_vars (thy : t') vs =
    VarSet.subset vs thy.true_vars

  let test_branch (thy : t') (vars, eqs) =
    test_vars thy vars && test_eqs thy eqs

  (** [reduced_vars] takes out redundant cofibration variables. *)
  let reduce_vars (thy : t') vars =
    VarSet.diff vars thy.true_vars

  (** [reduce_eqs] detects inconsistency of an equation set and takes out
    * redundant equations. *)
  let reduce_eqs (thy : t') eqs =
    let go ((thy', eqs) as acc) eq =
      match unsafe_test_and_assume_eq thy' eq with
      | true, _ -> acc
      | false, thy' -> thy',  Snoc (eqs, eq)
    in
    let thy', eqs = List.fold_left ~f:go ~init:(thy, Emp) eqs in
    match test_eq thy' (Dim0, Dim1) with
    | true -> `Inconsistent
    | false -> `Consistent (thy', Bwd.to_list eqs)

  (** [reduce_branch] detects inconsistency of a branch and takes out redundant
    * cofibration variables and equations. *)
  let reduce_branch (thy' : t') (vars, eqs) =
    match reduce_eqs thy' eqs with
    | `Inconsistent -> `Inconsistent
    | `Consistent (thy', eqs) ->
      `Consistent (assume_vars thy' vars, (reduce_vars thy' vars, eqs))

  (** [reduce_branches] removes inconsistent branches and takes out redundant
    * cofibration variables and equations. *)
  let reduce_branches (thy' : t') branches : cached_branches =
    let go branch =
      match reduce_branch thy' branch with
      | `Inconsistent -> None
      | `Consistent (thy', branch) -> Some (thy', branch)
    in
    List.filter_map ~f:go branches

  (** [drop_useless_branches] drops the branches that could be dropped without
    * affecting the coverages. *)
  let drop_useless_branches cached_branches : cached_branches =
    let go_fwd acc (thy', branch) =
      if Bwd.exists (fun (_, branch) -> test_branch thy' branch) acc then
        acc
      else
        Snoc (acc, (thy', branch))
    in
    let cached_branches = List.fold_left ~f:go_fwd ~init:Emp cached_branches in
    let go_bwd (thy', branch) acc =
      if List.exists ~f:(fun (_, branch) -> test_branch thy' branch) acc then
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
      | [vars, []] when VarSet.is_empty vars -> [`Consistent thy']
      | dissected_cofs ->
        List.map ~f:(fun (thy', _) -> `Consistent thy') @@
        drop_useless_branches @@
        reduce_branches thy' dissected_cofs

  (** [test] checks whether a cofibration is true within an algebraic theory *)
  let rec test (thy' : alg_thy') : cof -> bool =
    function
    | Cof.Cof phi ->
      begin
        match phi with
        | Cof.Eq (r, s) ->
          test_eq thy' (r, s)
        | Cof.Join phis ->
          List.exists ~f:(test thy') phis
        | Cof.Meet phis ->
          List.for_all ~f:(test thy') phis
      end
    | Cof.Var v ->
      test_var thy' v

  let left_invert_under_cofs ~zero ~seq (thy : t) cofs cont =
    match split thy cofs with
    | [] -> zero
    | [thy] -> cont thy
    | thys -> seq cont thys

  (* "unsafe" because consistency is not checked *)
  let unsafe_meet2' thy'1 thy'2 =
    {classes = UF.merge thy'1.classes thy'2.classes;
     true_vars = VarSet.union thy'1.true_vars thy'2.true_vars}

  let meet2 thy1 thy2 =
    match thy1, thy2 with
    | `Inconsistent, _ | _, `Inconsistent -> `Inconsistent
    | `Consistent thy'1, `Consistent thy'2 ->
      let thy' = unsafe_meet2' thy'1 thy'2 in
      match test_eq thy' (Dim0, Dim1) with
      | true -> `Inconsistent
      | false -> `Consistent thy'
end

module Disj =
struct
  type t = disj_thy

  let envelop_alg' alg_thy' : disj_thy =
    [alg_thy', (VarSet.empty, [])]

  let envelope_alg =
    function
    | `Consistent alg_thy' -> envelop_alg' alg_thy'
    | `Inconsistent -> []


  let empty : t = [Alg.emp', (VarSet.empty, [])]

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
      let go vars0 (_, (vars1, _)) = VarSet.inter vars0 vars1 in
      match cached_branches with
      | [] -> VarSet.empty
      | (_, (vars, _)) :: branches -> List.fold_left ~f:go ~init:vars branches
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
    let useful eq =
      List.exists cached_branches
        ~f:(fun (thy', _) -> not @@ Alg.test_eq thy' eq)
    in
    (* revisit all branches and remove all useless ones identified by the simple criterion above. *)
    List.map cached_branches
      ~f:(fun (thy', (vars, eqs)) -> thy', (VarSet.diff vars common_vars, List.filter ~f:useful eqs))

  (** [split thy cofs] adds to the theory [thy] the conjunction of a list of cofibrations [cofs]
    * and calculate the branches accordingly. This is similar to [Alg.split] in the spirit but
    * differs in detail. *)
  let split (thy : t) (cofs : cof list) : t =
    match dissect_cofibrations cofs with
    | [] -> []
    | [vars, []] when VarSet.is_empty vars -> thy
    | dissected_cofs ->
      Alg.drop_useless_branches @@
      List.concat_map thy
        ~f:(fun (thy', (vars, eq)) ->
            List.map (Alg.reduce_branches thy' dissected_cofs)
              ~f:(fun (thy', (sub_vars, sub_eqs)) ->
                  thy', (VarSet.union vars sub_vars, eq @ sub_eqs)))

  (** [assume thy cofs] is the same as [split thy cofs] except that it further refactors the
    * branches to optimize future searching. *)
  let assume (thy : t) (cofs : cof list) : t =
    refactor_branches @@ split thy cofs

  let test_sequent thy cx cof =
    List.for_all ~f:(fun thy' -> Alg.test thy' cof) @@
    List.map ~f:(fun (thy', _) -> thy') @@
    split thy cx

  let left_invert ~zero ~seq thy cont =
    match List.map thy ~f:(fun (thy', _) -> `Consistent thy') with
    | [] -> zero
    | [thy'] -> cont thy'
    | thy's -> seq cont thy's
end
