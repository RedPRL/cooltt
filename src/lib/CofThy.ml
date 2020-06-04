open CoolBasis

open Dim

type cof = (Dim.dim, int) Cof.cof

module UF = DisjointSet.Make (PersistentTable.M)
module VarSet = Set.Make (Int)

(** A presentation of an algebraic theory over the language of intervals and cofibrations. *)
type alg_thy' =
  { classes : dim UF.t;
    (** equivalence classes of dimensions *)

    true_vars : VarSet.t
  }

(** A presentation of a disjunctive theory over the language of intervals and cofibrations. *)
type disj_thy' =
  { classes : dim UF.t;
    (** equivalence classes of dimensions *)

    true_vars : VarSet.t;
    (** set of cofibration variables assumed to be true *)

    irreducible_joins : cof list list;
    (** a stack of irreducible joins, each represented by a list of cofibrations *)
  }

(* As an optimization, we remember when a theory is consistent or not. *)

type alg_thy = [ `Consistent of alg_thy' | `Inconsistent ]
type disj_thy = [ `Consistent of disj_thy' | `Inconsistent ]

let disj_thy'_of_alg_thy' : alg_thy' -> disj_thy' =
  fun {classes; true_vars} -> {classes; true_vars; irreducible_joins = []}

let disj_thy_of_alg_thy : alg_thy -> disj_thy =
  function
  | `Consistent alg_thy' -> `Consistent (disj_thy'_of_alg_thy' alg_thy')
  | `Inconsistent -> `Inconsistent

let init () =
  `Consistent
    {classes = UF.init ~size:100;
     true_vars = VarSet.empty;
     irreducible_joins = []}

let consistency =
  function
  | `Consistent _ -> `Consistent
  | `Inconsistent -> `Inconsistent

let find_class classes r =
  try UF.find r classes with _ -> r

module SearchHelper :
sig
  (** Pushes cofibrations into the theory.
      Invariant: input thy.classes must be consistent.

      @return If the [thy.classes] would be inconsistent, [None] is returned.
      Otherwise, [Some thy] is returned and [thy.classes] will be consistent. *)
  val push_cofs : disj_thy' -> cof list -> disj_thy' option

  (** Checking whether the [disj_thy'] is consistent.
      Invariant: input [thy.classes] must be consistent;
      the inconsistency can only come from [thy.irreducible_joins.] *)
  val is_consistent : disj_thy' -> bool
end
=
struct
  let rec push_cofs ({classes; true_vars; irreducible_joins} as thy) =
    function
    | [] -> Some thy
    | phi :: phis ->
      match phi with
      | Cof.Var v ->
        push_cofs {thy with true_vars = VarSet.add v true_vars} phis
      | Cof.Cof phi ->
        match phi with
        | Cof.Meet psis ->
          push_cofs thy @@ psis @ phis
        | Cof.Join psis ->
          push_cofs {thy with irreducible_joins = psis :: irreducible_joins} phis
        | Cof.Eq (r, s) ->
          let classes = UF.union r s classes in
          if UF.find Dim0 classes = UF.find Dim1 classes then
            None
          else
            push_cofs {thy with classes} phis

  (** [is_consistent] is almost a duplicate of the most general search. It exists because
    * (1) it's a clean way to avoid checking consistency within consistency and
    * (2) it's a clean way to avoid recursive modules. *)
  let rec is_consistent ({irreducible_joins; _} as thy) =
    match irreducible_joins with
    | [] -> true
    | psis :: irreducible_joins ->
      psis |> List.exists @@ fun psi ->
      Option.fold ~none:false ~some:is_consistent @@
      push_cofs {thy with irreducible_joins} [psi]
end

module Search :
sig
  (** Search all branches assuming more cofibrations. *)
  val left_invert
    : zero:'a
    (** [zero] is the default value for vacuous cases. *)
    -> seq:((cof -> 'a) -> cof list -> 'a)
    (** [seq] is the sequencing operator. *)
    -> fast_track:((unit -> 'a) -> (unit -> 'a) -> 'a)
    (** If the first component returns a "good" result, then don't bother with the second. (???) *)
    -> disj_thy
    -> cof list
    -> (alg_thy' -> 'a)
    -> 'a
end =
struct
  let left_invert' ~zero ~seq ~fast_track (thy : disj_thy') phis cont =
    let rec go =
      function
      | None -> zero
      | Some ({classes; true_vars; irreducible_joins} as thy) ->
        fast_track (fun _ -> cont {classes; true_vars}) @@ fun _ ->
        match irreducible_joins with
        | [] -> cont {classes; true_vars}
        | psis :: irreducible_joins when SearchHelper.is_consistent thy ->
          psis |> seq @@ fun psi ->
          go @@ SearchHelper.push_cofs {thy with irreducible_joins} [psi]
        | _ ->
          zero
    in
    go @@ SearchHelper.push_cofs thy phis

  let left_invert ~zero ~seq ~fast_track thy phis cont =
    match thy with
    | `Inconsistent -> zero
    | `Consistent thy -> left_invert' ~zero ~seq ~fast_track thy phis cont
end


(* Invariant: local.classes must be consistent. *)
let rec test (local : alg_thy') : cof -> bool =
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

let test_sequent thy cx phi =
  let fast_track x y = if x () then true else y () in
  Search.left_invert ~zero:true ~seq:List.for_all ~fast_track thy cx @@ fun thy ->
  test thy phi

let assume thy phis =
  match thy with
  | `Inconsistent -> `Inconsistent
  | `Consistent thy ->
    match SearchHelper.push_cofs thy @@ List.map Cof.reduce phis (* do we want Cof.reduce here? *) with
    | None -> `Inconsistent
    | Some thy ->
      if SearchHelper.is_consistent thy
      then `Consistent thy
      else `Inconsistent

let left_invert_under_cofs ~zero ~seq thy phis cont =
  Search.left_invert ~zero ~seq ~fast_track:(fun _ x -> x ()) thy phis @@ fun alg_thy' ->
  cont @@ `Consistent (disj_thy'_of_alg_thy' alg_thy')


module Algebraic =
struct
  let init () =
    `Consistent
      {classes = UF.init ~size:100;
       true_vars = VarSet.empty}

  let consistency =
    function
    | `Consistent _ -> `Consistent
    | `Inconsistent -> `Inconsistent

  let disj_envelope = disj_thy_of_alg_thy

  let partition_thy =
    function
    | `Inconsistent -> `Inconsistent, []
    | `Consistent {classes; true_vars; irreducible_joins} ->
      `Consistent {classes; true_vars}, List.map Cof.join irreducible_joins

  let assemble_thy alg_thy =
    assume @@ disj_envelope alg_thy

  let left_invert_under_cofs ~zero ~seq alg_thy phis cont =
    Search.left_invert ~zero ~seq ~fast_track:(fun _ x -> x ()) (disj_envelope alg_thy) phis @@ fun alg_thy' ->
    cont @@ `Consistent alg_thy'
end
