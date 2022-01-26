open Basis
open Core
open Frontend

open Framework

open Monad.Notation (RM)

(** The telescope for a monoid (without laws!) *)
let monoid_tele _ =
  RM.lift_cmp @@
  Sem.splice_tm @@
  Splice.term @@
  TB.cons (`User ["carrier"]) TB.code_univ @@ TB.lam ~ident:(`User ["carrier"]) @@ fun el_carrier ->
  let carrier = TB.el_out el_carrier in
  TB.cons (`User ["mul"]) (TB.code_pis [carrier; TB.lam @@ fun _ -> carrier] @@ fun _ -> carrier) @@ TB.lam ~ident:(`User ["mul"]) @@ fun _ ->
  TB.cons (`User ["unit"]) carrier @@ TB.lam ~ident:(`User ["unit"]) @@ fun _ ->
  TB.nil

(** The telescope for a group (without laws!) *)
let group_tele _ =
  RM.lift_cmp @@
  Sem.splice_tm @@
  Splice.term @@
  TB.cons (`User ["carrier"]) TB.code_univ @@ TB.lam ~ident:(`User ["carrier"]) @@ fun el_carrier ->
  let carrier = TB.el_out el_carrier in
  TB.cons (`User ["mul"]) (TB.code_pis [carrier; TB.lam @@ fun _ -> carrier] @@ fun _ -> carrier) @@ TB.lam ~ident:(`User ["mul"]) @@ fun _ ->
  TB.cons (`User ["unit"]) carrier @@ TB.lam ~ident:(`User ["unit"]) @@ fun _ ->
  TB.cons (`User ["inv"]) (TB.code_pis [carrier] @@ fun _ -> carrier) @@ TB.lam ~ident:(`User ["inv"]) @@ fun _ ->
  TB.nil

(** Test that we can elaborate the telescope of a monoid properly. *)
let tele_elab_monoid () =
  let actual _ =
    let tac =
      R.Telescope.cons (`User ["carrier"]) R.Univ.univ @@ R.Pi.intro ~ident:(`User ["carrier"]) @@ fun carrier ->
      let tac_carrier = T.Chk.syn @@ R.El.elim @@ T.Var.syn carrier in
      R.Telescope.cons (`User ["mul"]) (Tactics.Pi.intros [`Anon, tac_carrier; `Anon, tac_carrier] tac_carrier) @@ R.Pi.intro ~ident:(`User ["mul"]) @@ fun _ ->
      R.Telescope.cons (`User ["unit"]) tac_carrier @@ R.Pi.intro ~ident:(`User ["unit"]) @@ fun _ ->
      R.Telescope.nil
    in
    let* tele = T.Chk.run tac D.Telescope in
    RM.lift_ev @@ Sem.eval tele
  in
  Alcotest.check (check_tm [] (RM.ret D.Telescope))
    "elaborate the telescope of a monoid"
    monoid_tele
    actual

(** Test that telescope elimination works as expected. *)
let tele_elim_unfold () =
  let expected [] =
    RM.lift_cmp @@
    Sem.splice_tm @@
    Splice.term @@
    TB.code_pi TB.code_univ @@ TB.lam ~ident:(`User ["carrier"]) @@ fun el_carrier ->
    let carrier = TB.el_out el_carrier in
    TB.code_pi (TB.code_pis [carrier; TB.lam @@ fun _ -> carrier] @@ fun _ -> carrier) @@ TB.lam ~ident:(`User ["mul"]) @@ fun _ ->
    TB.code_pi carrier @@ TB.lam ~ident:(`User ["unit"]) @@ fun _ ->
    TB.code_univ
  in
  let actual [] =
    let* tele = monoid_tele [] in
    RM.lift_cmp @@
    Sem.splice_tm @@
    Splice.con tele @@ fun tele ->
    Splice.term @@
    let cons_case =
      TB.lam ~ident:(`User ["A"]) @@ fun a ->
      TB.lam @@ fun _ ->
      TB.lam ~ident:(`User ["B"]) @@ fun b ->
      TB.code_pi a @@ TB.lam ~ident:(`User ["a"]) @@ fun ax ->
      TB.ap b [ax]
    in
    TB.tele_elim (TB.lam @@ fun _ -> TB.code_univ) TB.code_univ cons_case tele
  in
  Alcotest.check (check_tm [] (RM.ret D.Telescope))
    "telescope elimination works"
    expected
    actual

let () =
  let open Alcotest in
  Debug.debug_mode true;
  run "Records" [
    "Telescope Elaboration", [
      test_case "tele/elab/monoid" `Quick tele_elab_monoid
    ];
    "Telescope Elimination", [
      test_case "tele/elim/unfold" `Quick tele_elim_unfold
    ]
  ]
