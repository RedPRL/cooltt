open Basis
open Bwd
open Z3Solver

type cof = CofThyData.cof

module Alg =
struct
  type t = cof list

  exception Z3Failure

  let empty : t = []

  let bot : t = [Cof.bot]

  let dump fmt thy =
    Format.fprintf fmt "@[<v1>[%a]@]"
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.pp_print_cut fmt ())
         CofThyData.dump_cof)
      thy

  let memoize store f x =
    match Hashtbl.find_opt store x with
    | Some x -> x
    | None -> let res = f x in Hashtbl.replace store x res; res

  let test_sequent_store : (t * cof option, [`Consistent | `Inconsistent]) Hashtbl.t = Hashtbl.create 1000
  let test_sequent ?rhs ~lhs : [`Consistent | `Inconsistent] =
    (* Format.printf "Checking %a@." dump thy;
       begin
       match neg with
       | None -> ()
       | Some cof -> Format.printf "  with negated %a@." CofThyData.dump_cof cof
       end; *)
    (lhs, rhs) |> memoize test_sequent_store @@ fun (lhs, rhs) ->
    match test_sequent ?rhs ~lhs with
    | UNSATISFIABLE -> `Inconsistent
    | SATISFIABLE -> `Consistent
    | UNKNOWN -> raise Z3Failure
  let consistency (thy : t) : [`Consistent | `Inconsistent] =
    test_sequent ?rhs:None ~lhs:thy

  let test (thy : t) cof =
    (* Format.printf "Calling consistency from test_sequent@."; *)
    match test_sequent ~rhs:cof ~lhs:thy with
    | `Inconsistent -> true
    | `Consistent -> false

  let insert cof (thy : t) =
    (* XXX use CCOrd *)
    let sorted_thy = List.merge
        (fun c1 c2 ->
           match compare (Cof.complexity_cof c1) (Cof.complexity_cof c2) with
           | 0 -> compare c1 c2
           | i -> i)
        [cof] thy in
    let reduced_thy_bwd =
      List.fold_left (fun reduced cof ->
          if test (Bwd.to_list reduced) cof then
            reduced
          else
            Snoc (reduced, cof))
        Emp sorted_thy
    in
    Bwd.to_list reduced_thy_bwd

  let assume1 thy cof : t =
    match consistency thy with
    | `Consistent -> insert cof thy
    | `Inconsistent -> bot

  let assume thy cofs : t =
    List.fold_left assume1 thy cofs

  let left_invert_under_cofs ~zero ~seq:_ thy cofs k =
    let thy' = assume thy cofs in
    match consistency thy' with
    | `Inconsistent -> zero
    | `Consistent -> k thy'

end

module Disj =
struct
  include Alg

  let envelope_alg (alg : t) = alg

  let test_sequent (thy : t) cofs cof =
    test (assume thy cofs) cof

  let left_invert ~zero ~seq thy k =
    (* Format.printf "Calling left_invert_under_cofs from left_invert@."; *)
    left_invert_under_cofs ~zero ~seq thy [] k
end
