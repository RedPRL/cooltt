open Basis
open Bwd
open BwdNotation

(* thin wrappers of raw OCaml API *)
module Z3Raw =
struct
  type context = Z3.context
  let context = Z3.mk_context []

  type solver = Z3.Solver.solver
  type result = Z3.Solver.status =
      UNSATISFIABLE | UNKNOWN | SATISFIABLE
  let mk_solver () = Z3.Solver.mk_simple_solver context
  let add_asserts solver exprs = Z3.Solver.add solver exprs
  let copy_solver solver = Z3.Solver.translate solver context
  let check solver exprs = Z3.Solver.check solver exprs

  type symbol = Z3.Symbol.symbol
  let mk_symbol_s s = Z3.Symbol.mk_string context s

  type sort = Z3.Sort.sort
  let mk_sort_s s = Z3.Sort.mk_uninterpreted_s context s
  let mk_real () = Z3.Arithmetic.Real.mk_sort context
  let mk_bool () = Z3.Boolean.mk_sort context

  type expr = Z3.Expr.expr
  let mk_ite e1 e2 e3 = Z3.Boolean.mk_ite context e1 e2 e3
  let mk_le e1 e2 = Z3.Arithmetic.mk_le context e1 e2
  let mk_eq e1 e2 = Z3.Boolean.mk_eq context e1 e2
  let mk_and es = Z3.Boolean.mk_and context es
  let mk_real_numeral_i i = Z3.Arithmetic.Real.mk_numeral_i context i

  type quantifier = Z3.Quantifier.quantifier
  let mk_bound i sort = Z3.Quantifier.mk_bound context i sort
  let expr_of_quantifier = Z3.Quantifier.expr_of_quantifier
  let mk_forall ~sorts ~symbols ~body : quantifier =
    Z3.Quantifier.mk_forall context sorts symbols body None [] [] None None

  type func_decl = Z3.FuncDecl.func_decl
  let mk_func_decl ~name ~domain ~range : func_decl =
    Z3.FuncDecl.mk_func_decl context name domain range
  let apply func args = Z3.FuncDecl.apply func args
end

(* smart builder for various components *)
module Z3Builder =
struct
  type sort = II | FF | Real | Bool
  type symbol = string
  type expr =
    | Bound of int (* de Bruijn {b LEVELS} *)
    | Ite of expr * expr * expr
    | Le of expr * expr
    | Eq of expr * expr
    | And of expr list
    | RealNumeral of int
    | Forall of (symbol * sort) list * expr
    | Apply of symbol * expr list

  let dim = II
  let cof = FF
  let real = Real
  let (!%) l = Bound l
  let (!) nm = Apply (nm, [])
  let ite e1 e2 e3 = Ite (e1, e2, e3)
  let (<=) e1 e2 = Le (e1, e2)
  let (=) e1 e2 = Eq (e1, e2)
  let (&&) e1 e2 = And [e1; e2]
  let num i = RealNumeral i
  let forall bs body = Forall (bs, body)
  let ($) f args = Apply (f, args)

  let memoize store f x =
    match Hashtbl.find_opt store x with
    | Some x -> x
    | None -> let res = f x in Hashtbl.replace store x res; res

  let sort_store : (sort, Z3Raw.sort) Hashtbl.t = Hashtbl.create 10
  let sort =
    memoize sort_store @@ function
    | II -> Z3Raw.mk_sort_s "II"
    | FF -> Z3Raw.mk_sort_s "FF"
    | Real -> Z3Raw.mk_real ()
    | Bool -> Z3Raw.mk_bool ()

  let symbol_store : (symbol, Z3Raw.symbol) Hashtbl.t = Hashtbl.create 100
  let symbol = memoize symbol_store Z3Raw.mk_symbol_s

  let decl_store : (symbol, Z3.FuncDecl.func_decl) Hashtbl.t = Hashtbl.create 10
  let func_decl ~name ~domain ~range =
    name |> begin
      memoize decl_store @@ fun name ->
      let name = symbol name in
      let domain = List.map sort domain in
      let range = sort range in
      Z3Raw.mk_func_decl ~name ~domain ~range
    end
  let const_decl ~name ~range =
    func_decl ~name ~domain:[] ~range

  let get_decl_by_name sym =
    Hashtbl.find decl_store sym

  let expr_store : (sort bwd * expr, Z3Raw.expr) Hashtbl.t = Hashtbl.create 100
  let expr =
    let rec loop env e =
      (env, e) |> memoize expr_store @@ fun (env, e) ->
      match e with
      | Bound l ->
        let i = Bwd.length env - l in
        let s = Bwd.nth env i in
        Z3Raw.mk_bound i (sort s)
      | Ite (e1, e2, e3) -> Z3Raw.mk_ite (loop env e1) (loop env e2) (loop env e3)
      | Le (e1, e2) -> Z3Raw.mk_le (loop env e1) (loop env e2)
      | Eq (e1, e2) -> Z3Raw.mk_eq (loop env e1) (loop env e2)
      | And es -> Z3Raw.mk_and @@ List.map (loop env) es
      | RealNumeral i -> Z3Raw.mk_real_numeral_i i
      | Forall (binders, body) ->
        let symbols, sorts = List.split binders in
        let symbols = List.map symbol symbols in
        let body = loop (env <>< sorts) body in
        let sorts = List.map sort sorts in
        Z3Raw.expr_of_quantifier @@ Z3Raw.mk_forall ~sorts ~symbols ~body
      | Apply (sym, args) ->
        let func = get_decl_by_name sym in
        let args = List.map (loop env) args in
        Z3Raw.apply func args
    in
    loop Emp

  let pp_sort fmt : sort -> unit =
    function
    | II -> Uuseg_string.pp_utf_8 fmt "𝕀"
    | FF -> Uuseg_string.pp_utf_8 fmt "𝔽"
    | Real -> Uuseg_string.pp_utf_8 fmt "ℝ"
    | Bool -> Uuseg_string.pp_utf_8 fmt "𝔹"

  let pp_symbol fmt str =
    Format.pp_print_string fmt @@ String.escaped str

  let rec pp_expr fmt =
    function
    | Bound l -> Format.fprintf fmt "bound[%i]" l
    | Ite (e1, e2, e3) -> Format.fprintf fmt "ite[%a;%a;%a]" pp_expr e1 pp_expr e2 pp_expr e3
    | Le (e1, e2) -> Format.fprintf fmt "le[%a;%a]" pp_expr e1 pp_expr e2
    | Eq (e1, e2) -> Format.fprintf fmt "eq[%a;%a]" pp_expr e1 pp_expr e2
    | And es ->
      Format.fprintf fmt "and[%a]"
        (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_char fmt ';') pp_expr) es
    | RealNumeral i -> Format.fprintf fmt "real[%i]" i
    | Forall (binders, body) ->
      Format.fprintf fmt "forall[%a%a]"
        (fun fmt -> List.iter @@ fun (symbol, sort) -> Format.fprintf fmt "%a;%a;" pp_symbol symbol pp_sort sort)
        binders
        pp_expr body
    | Apply (sym, args) ->
      Format.fprintf fmt "apply[%a%a]"
        pp_symbol sym
        (fun fmt -> List.iter @@ Format.fprintf fmt ";%a" pp_expr) args
end

(* the high-level interface *)
module Z3Monad =
struct
  module R = Basis.Monad.MonadReaderResult(struct type local = Z3Raw.solver end)
  type 'a m = 'a R.m
  let bind = R.bind
  let ret = R.ret

  let base_solver =
    let base_solver = Z3Raw.mk_solver () in

    (* (define-const bot Real 0.0) *)
    let _ = Z3Builder.const_decl ~name:"bot" ~range:Real in
    let () = Z3Raw.add_asserts base_solver
        [Z3Builder.(expr (!"bot" = num 0))]
    in

    (* (define-const top Real 1.0) *)
    let _ = Z3Builder.const_decl ~name:"top" ~range:Real in
    let () = Z3Raw.add_asserts base_solver
        [Z3Builder.(expr (!"top" = num 1))]
    in

    (* (define-fun in-range ((i Real)) Bool (<= bot i top)) *)
    let _ = Z3Builder.func_decl ~name:"in-range" ~domain:[Real] ~range:Bool in
    let () = Z3Raw.add_asserts base_solver
        [Z3Builder.(expr @@
                    forall ["i", Real]
                      ("in-range" $[!%0] = !"bot" <= !%0 && !%0 <= !"top"))]
    in

    (* (define-fun land ((i Real) (j Real)) Real (ite (<= i j) i j)) *)
    let _ = Z3Builder.func_decl ~name:"land" ~domain:[Real; Real] ~range:Real in
    let () = Z3Raw.add_asserts base_solver
        [Z3Builder.(expr @@
                    forall ["i", Real; "j", Real]
                      ("land" $[!%0; !%1] = (ite (!%0 <= !%1) !%0 !%1)))]
    in

    (* (define-fun lor ((i Real) (j Real)) Real (ite (<= i j) j i)) *)
    let _ = Z3Builder.func_decl ~name:"lor" ~domain:[Real; Real] ~range:Real in
    let () = Z3Raw.add_asserts base_solver
        [Z3Builder.(expr @@
                    forall ["i", Real; "j", Real]
                      ("lor" $[!%0; !%1] = (ite (!%0 <= !%1) !%1 !%0)))]
    in

    (* (define-fun arrow ((i Real) (j Real)) Real (ite (<= i j) top j)) *)
    let _ = Z3Builder.func_decl ~name:"arrow" ~domain:[Real; Real] ~range:Real in
    let () = Z3Raw.add_asserts base_solver
        [Z3Builder.(expr @@
                    forall ["i", Real; "j", Real]
                      ("arrow" $[!%0; !%1] = (ite (!%0 <= !%1) !"top" !%1)))]
    in

    (* (define-fun neg ((i Real)) Real (arrow i bot)) *)
    let _ = Z3Builder.func_decl ~name:"neg" ~domain:[Real] ~range:Real in
    let () = Z3Raw.add_asserts base_solver
        [Z3Builder.(expr @@ forall ["i", Real] ("arrow" $[!%0; !"bot"]))]
    in

    (* (define-fun is-true ((i Real)) Bool (= i top)) *)
    let _ = Z3Builder.func_decl ~name:"is-true" ~domain:[Real] ~range:Bool in
    let () = Z3Raw.add_asserts base_solver
        [Z3Builder.(expr @@ forall ["i", Real] (!%0 = !"top"))]
    in

    (* (define-fun is-false ((i Real)) Bool (= i bot)) *)
    let _ = Z3Builder.func_decl ~name:"is-false" ~domain:[Real] ~range:Bool in
    let () = Z3Raw.add_asserts base_solver
        [Z3Builder.(expr @@ forall ["i", Real] (!%0 = !"top"))]
    in

    (* (declare-const one I) *)
    let _ = Z3Builder.const_decl ~name:"one" ~range:II in

    (* (declare-const zero I) *)
    let _ = Z3Builder.const_decl ~name:"zero" ~range:II in

    (* (declare-fun eq (I I) Real) *)
    let _ = Z3Builder.func_decl ~name:"eq" ~domain:[II; II] ~range:Real in

    (* (assert (forall ((i I) (j I)) (in-range (eq i j)))) *)
    let () = Z3Raw.add_asserts base_solver
        [Z3Builder.(expr @@ forall ["i", II; "j", II] ("in-range" $["eq" $[!%0; !%1]]))]
    in

    (* (assert (forall ((i I)) (= (eq i i) top))) *)
    let () = Z3Raw.add_asserts base_solver
        [Z3Builder.(expr @@ forall ["i", II] ("eq" $[!%0; !%0] = !"top"))]
    in

    (* (assert (forall ((i I) (j I)) (= (eq i j) (eq j i)))) *)
    let () = Z3Raw.add_asserts base_solver
        [Z3Builder.(expr @@ forall ["i", II; "j", II] (("eq" $[!%0; !%1]) = ("eq" $[!%1; !%0])))]
    in

    (* (assert (forall ((i I) (j I) (k I)) (is-true (arrow (land (eq i j) (eq j k)) (eq i k))))) *)
    let () = Z3Raw.add_asserts base_solver
        [Z3Builder.(expr @@
                    forall ["i", II; "j", II; "k", II]
                      ("is-true" $["arrow" $["eq" $[!%0; !%1] && "eq" $[!%1; !%2]; "eq" $[!%0; !%2]]]))]
    in

    (* (assert (is-false (eq one zero))) *)
    let () = Z3Raw.add_asserts base_solver
        [Z3Builder.(expr ("is-false" $["eq" $[!"one"; !"zero"]]))]
    in

    (* (declare-fun val (F) Real) *)
    let _ = Z3Builder.func_decl ~name:"val" ~domain:[FF] ~range:Real in

    (* (assert (forall ((f F)) (in-range (val f)))) *)
    let () = Z3Raw.add_asserts base_solver
        [Z3Builder.(expr (forall ["f", FF] ("in-range" $["val" $[!%0]])))]
    in

    base_solver
end
