open CoolBasis
open Bwd
open Dim

type cof = (Dim.dim, int) Cof.cof

module UF = DisjointSet.Make (struct type t = dim let compare = compare end)
module VarSet = Set.Make (Int)

(** A presentation of an algebraic theory over the language of intervals and cofibrations. *)
type alg_thy' =
  { classes : UF.t;
    (** equivalence classes of dimensions *)

    true_vars : VarSet.t
  }

type eq = Dim.dim * Dim.dim
type branch = VarSet.t * eq list
type branches = branch list
type cached_branch = alg_thy' * branch
type cached_branches = cached_branch list

(* As an optimization, we remember when a theory is consistent or not. *)

type alg_thy = [ `Consistent of alg_thy' | `Inconsistent ]
type disj_thy = cached_branches

let rec disect_cofibrations : cof list -> branches =
  function
  | [] -> [VarSet.empty, []]
  | cof :: cofs ->
    match cof with
    | Cof.Var v ->
      List.map (fun (vars, eqs) -> VarSet.add v vars, eqs) @@
      disect_cofibrations cofs
    | Cof.Cof cof ->
      match cof with
      | Cof.Meet meet_cofs ->
        disect_cofibrations @@ meet_cofs @ cofs
      | Cof.Join join_cofs ->
        join_cofs |> List.concat_map @@ fun join_cof ->
        disect_cofibrations @@ join_cof :: cofs
      | Cof.Eq (r, s) ->
        List.map (fun (vars, eqs) -> vars, (r, s) :: eqs) @@
        disect_cofibrations cofs

module Alg =
struct
  type t = alg_thy
  type t' = alg_thy'

  let init' =
    {classes = UF.init;
     true_vars = VarSet.empty}

  let init =
    `Consistent init'

  let consistency =
    function
    | `Consistent _ -> `Consistent
    | `Inconsistent -> `Inconsistent

  let disj_envelope' alg_thy' : disj_thy =
    [alg_thy', (VarSet.empty, [])]

  let disj_envelope =
    function
    | `Consistent alg_thy' -> disj_envelope' alg_thy'
    | `Inconsistent -> []

  let assume_eq (thy : t') (r, s) =
    let classes = UF.union r s thy.classes in
    if UF.find Dim0 classes = UF.find Dim1 classes then
      `Inconsistent
    else
      `Consistent {thy with classes}

  (* this is unsafe because it assumes the resulting thy is consistent *)
  let unsafe_assume_eq (thy : t') (r, s) =
    {thy with classes = UF.union r s thy.classes}

  let assume_vars (thy : t') vars =
    {thy with true_vars = VarSet.union vars thy.true_vars}

  let find_class classes r =
    try UF.find r classes with _ -> r

  let test_eq (thy : t') (r, s) =
    r = s || find_class thy.classes r = find_class thy.classes s

  let test_eqs (thy : t') eqs =
    List.for_all (test_eq thy) eqs

  let test_var (thy : t') v =
    VarSet.mem v thy.true_vars

  let test_vars (thy : t') vs =
    VarSet.subset vs thy.true_vars

  let test_branch (thy : t') (vars, eqs) =
    test_vars thy vars && test_eqs thy eqs

  let normalize_vars (thy : t') vars =
    VarSet.diff vars thy.true_vars

  let normalize_eqs (thy : t') eqs =
    let go acc eq =
      match acc with
      | `Inconsistent -> `Inconsistent
      | `Consistent (thy', eqs) ->
        if test_eq thy' eq then
          acc
        else
          match assume_eq thy' eq with
          | `Inconsistent -> `Inconsistent
          | `Consistent thy' -> `Consistent (thy', Snoc (eqs, eq))
    in
    match List.fold_left go (`Consistent (thy, Emp)) eqs with
    | `Inconsistent -> `Inconsistent
    | `Consistent (thy', eqs) -> `Consistent (thy', Bwd.to_list eqs)

  (* this is unsafe because it assumes the resulting thy is consistent *)
  let unsafe_normalize_eqs (thy' : t') eqs =
    let go (thy', eqs) eq =
      if test_eq thy' eq then
        thy', eqs
      else
        unsafe_assume_eq thy' eq, Snoc (eqs, eq)
    in
    let _, eqs = List.fold_left go (thy', Emp) eqs in
    Bwd.to_list eqs

  let normalize_branch (thy' : t') (vars, eqs) =
    match normalize_eqs thy' eqs with
    | `Inconsistent -> `Inconsistent
    | `Consistent (thy', eqs) ->
      `Consistent (assume_vars thy' vars, (normalize_vars thy' vars, eqs))

  (* this is unsafe because it assumes the resulting thy is consistent *)
  let unsafe_normalize_branch (thy' : t') (vars, eqs) =
    normalize_vars thy' vars, unsafe_normalize_eqs thy' eqs

  let rec test (thy' : alg_thy') : cof -> bool =
    function
    | Cof.Cof phi ->
      begin
        match phi with
        | Cof.Eq (r, s) ->
          test_eq thy' (r, s)
        | Cof.Join phis ->
          List.exists (test thy') phis
        | Cof.Meet phis ->
          List.for_all (test thy') phis
      end
    | Cof.Var v ->
      test_var thy' v

  let shrink_branches (thy' : t') branches : cached_branches =
    (* stage 1.1: shrink branches *)
    let go branch =
      match normalize_branch thy' branch with
      | `Inconsistent -> None
      | `Consistent (thy', branch) -> Some (thy', branch)
    in
    List.filter_map go branches

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

  let split (thy : t) (cofs : cof list) : t list =
    match thy with
    | `Inconsistent -> []
    | `Consistent thy' ->
      match disect_cofibrations cofs with
      | [] -> []
      | [vars, []] when VarSet.is_empty vars -> [`Consistent thy']
      | disected_cofs ->
        let cached_branches =
          drop_useless_branches @@
          shrink_branches thy' disected_cofs in
        List.map (fun (thy', _) -> `Consistent thy') cached_branches

  let left_invert_under_cofs ~zero ~seq (thy : t) cofs cont =
    match split thy cofs with
    | [] -> zero
    | [thy] -> cont thy
    | thys -> seq cont thys
end

module Disj =
struct
  type t = disj_thy

  let init : t = [Alg.init', (VarSet.empty, [])]

  let consistency =
    function
    | [] -> `Inconsistent
    | _ -> `Consistent

  (* favonia: this optimization seems to be too costly? *)
  let rebase_branch cached_branches : t =
    let common_vars =
      let go vars0 (_, (vars1, _)) = VarSet.inter vars0 vars1 in
      match cached_branches with
      | [] -> VarSet.empty
      | (_, (vars, _)) :: branches -> List.fold_left go vars branches
    in
    let useful eq = cached_branches |> List.exists @@ fun (thy', _) -> not @@ Alg.test_eq thy' eq in
    cached_branches |> List.map @@ fun (thy', (vars, eqs)) ->
    thy', (VarSet.diff vars common_vars, List.filter useful eqs)

  let split (thy : t) (cofs : cof list) : cached_branches =
    match disect_cofibrations cofs with
    | [] -> []
    | [vars, []] when VarSet.is_empty vars -> thy
    | disected_cofs ->
      let cached_branches =
        thy |> List.concat_map @@ fun (thy', (vars, eq)) ->
        Alg.shrink_branches thy' disected_cofs |> List.map @@ fun (thy', (sub_vars, sub_eqs)) ->
        thy', (VarSet.union vars sub_vars, eq @ sub_eqs)
      in
      Alg.drop_useless_branches cached_branches

  let assume (thy : t) (cofs : cof list) : t =
    rebase_branch @@ split thy cofs

  let test_sequent thy cx cof =
    let thy's = List.map (fun (thy', _) -> thy') @@ split thy cx in
    thy's |> List.for_all @@ fun thy' -> Alg.test thy' cof

  let left_invert ~zero ~seq thy cont =
    match List.map (fun (thy', _) -> `Consistent thy') thy with
    | [] -> zero
    | [thy'] -> cont thy'
    | thy's -> seq cont thy's
end
