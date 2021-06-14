open Basis
open Bwd
open Z3Monad
open Monad.Notation (Z3Monad)
module MU = Monad.Util (Z3Monad)

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

  let consistency_store : (t * cof option, [`Consistent | `Inconsistent]) Hashtbl.t = Hashtbl.create 1000
  let consistency_gen ?neg (thy : t) : [`Consistent | `Inconsistent] =
    Format.printf "Checking %a@." dump thy;
    begin
      match neg with
      | None -> ()
      | Some cof -> Format.printf "  with negated %a@." CofThyData.dump_cof cof
    end;
    (thy, neg) |> memoize consistency_store @@ fun (thy, neg) ->
    run_exn @@
    let* () = reset () in
    let* () = add_cofs thy in
    (* XXX use guard *)
    let* () = match neg with Some cof -> add_negated_cof cof | None -> ret () in
    check () |>> function
    | UNSATISFIABLE ->
      Format.printf "==> inconsistent@.";
      ret `Inconsistent
    | SATISFIABLE ->
      Format.printf "==> consistent@.";
      ret `Consistent
    | UNKNOWN ->
      let* reason = get_reason_unknown () in
      Format.printf "==> unknown %s@." reason;
      throw Z3Failure
  let consistency (thy : t) : [`Consistent | `Inconsistent] =
    let ans = consistency_gen ?neg:None thy in
    let real_ans = CofThy.Disj.(consistency (assume empty thy)) in
    assert (ans = real_ans);
    ans

  let test (thy : t) cof =
    Format.printf "Calling consistency from test_sequent@.";
    match consistency_gen ~neg:cof thy with
    | `Inconsistent ->
      Format.printf "==> true@.";
      let real_ans = CofThy.Disj.(test_sequent (assume empty thy) [] cof) in
      assert (real_ans = true);
      true
    | `Consistent ->
      Format.printf "==> false@.";
      let real_ans = CofThy.Disj.(test_sequent (assume empty thy) [] cof) in
      assert (real_ans = false);
      false

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
    Format.printf "Calling left_invert_under_cofs from left_invert@.";
    left_invert_under_cofs ~zero ~seq thy [] k
end
