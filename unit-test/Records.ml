open Basis
open Core
open Frontend

open Framework

open Monad.Notation (RM)

let tele_monoid () =
  let expected [] =
    RM.lift_cmp @@
    Sem.splice_tm @@
    Splice.term @@
    TB.cons (`User ["carrier"]) TB.code_univ @@ TB.lam ~ident:(`User ["carrier"]) @@ fun el_carrier ->
    let carrier = TB.el_out el_carrier in
    TB.cons (`User ["mul"]) (TB.code_pis [carrier; TB.lam @@ fun _ -> carrier] @@ fun _ -> carrier) @@ TB.lam ~ident:(`User ["mul"]) @@ fun _ ->
    TB.cons (`User ["unit"]) carrier @@ TB.lam ~ident:(`User ["unit"]) @@ fun _ ->
    TB.nil
  in
  let actual [] =
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
    expected
    actual

let () =
  let open Alcotest in
  run "Records" [
    "Telescope Elaboration", [
      test_case "tele/monoid/elab" `Quick tele_monoid
    ]
  ]
