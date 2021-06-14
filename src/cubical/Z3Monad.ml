open Basis
open Bwd
open BwdNotation

(* thin wrappers of raw OCaml API *)
module Z3Raw =
struct
  let context = Z3.mk_context []

  let mk_params () = Z3.Params.mk_params context
  let add_int_param = Z3.Params.add_int

  type result = Z3.Solver.status =
      UNSATISFIABLE | UNKNOWN | SATISFIABLE
  let mk_solver () = Z3.Solver.mk_solver context None
  let set_parameters = Z3.Solver.set_parameters
  let reset solver = Z3.Solver.reset solver
  let pop solver i = Z3.Solver.pop solver i
  let push solver = Z3.Solver.push solver
  let add_assertions solver exprs = Z3.Solver.add solver exprs
  let check solver exprs = Z3.Solver.check solver exprs
  let get_reason_unknown solver = Z3.Solver.get_reason_unknown solver
  let dump_solver solver = Format.printf "%s@." (Z3.Solver.to_string solver)

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
  let dump_func_decl d = Format.printf "%s@." (Z3.FuncDecl.to_string d)
end

(* hide the original API *)
module Z3 = struct end

module SolverBuilder =
struct
  let make () =
    let solver = Z3Raw.mk_solver () in
    let params = Z3Raw.mk_params () in
    Z3Raw.add_int_param params (Z3Raw.mk_symbol_s "solver2_timeout") 10;
    Z3Raw.set_parameters solver params;
    solver
end

module Lang =
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
    | Apply of [`Other of symbol | `Dim of symbol | `Cof of symbol] * expr list

  let dim = II
  let cof = FF
  let real = Real
  let (!%) l = Bound l
  let ite e1 e2 e3 = Ite (e1, e2, e3)
  let (<=) e1 e2 = Le (e1, e2)
  let (=) e1 e2 = Eq (e1, e2)
  let (&&) e1 e2 = And [e1; e2]
  let num i = RealNumeral i
  let forall bs body = Forall (bs, body)
  let ($) f args = Apply (`Other f, args)
end

module Store =
struct
  let sort_store : (Lang.sort, Z3Raw.sort) Hashtbl.t = Hashtbl.create 10
  let symbol_store : (Lang.symbol, Z3Raw.symbol) Hashtbl.t = Hashtbl.create 10
  let other_decl_store : (Lang.symbol, Z3Raw.func_decl) Hashtbl.t = Hashtbl.create 10
  let expr_store : (Lang.sort bwd * Lang.expr, Z3Raw.expr) Hashtbl.t = Hashtbl.create 100

  let memoize store f x =
    match Hashtbl.find_opt store x with
    | Some x -> x
    | None -> let ans = f x in Hashtbl.replace store x ans; ans
  let get store x = Hashtbl.find store x

  let dim_store : (int, Z3Raw.func_decl) Hashtbl.t = Hashtbl.create 10
  let dim_remapping : (string, int) Hashtbl.t = Hashtbl.create 10

  let cof_store : (int, Z3Raw.func_decl) Hashtbl.t = Hashtbl.create 10
  let cof_remapping : (string, int) Hashtbl.t = Hashtbl.create 10

  let memoize2 store remapping f x =
    match Hashtbl.find_opt remapping x with
    | Some n -> Hashtbl.find store n
    | None ->
      let next_index = Hashtbl.length remapping in
      Hashtbl.replace remapping x next_index;
      memoize store f next_index

  let get2 store mapping x =
    Hashtbl.find store (Hashtbl.find mapping x)

  let assert_empty_remappings () =
    assert (Hashtbl.length dim_remapping = 0);
    assert (Hashtbl.length cof_remapping = 0)

  let clear_remappings () =
    Hashtbl.clear expr_store; (* expressions can contain variables *)
    Hashtbl.clear dim_remapping;
    Hashtbl.clear cof_remapping
end

(* smart builders for various components *)
module Builder =
struct
  let sort =
    Store.(memoize sort_store) @@ function
    | II -> Z3Raw.mk_sort_s "II"
    | FF -> Z3Raw.mk_sort_s "FF"
    | Real -> Z3Raw.mk_real ()
    | Bool -> Z3Raw.mk_bool ()

  let symbol = Store.(memoize symbol_store) Z3Raw.mk_symbol_s

  let other_func_decl ~name ~domain ~range =
    name |> begin
      Store.(memoize other_decl_store) @@ fun name ->
      let name = symbol name in
      let domain = List.map sort domain in
      let range = sort range in
      Z3Raw.mk_func_decl ~name ~domain ~range
    end
  let other_const_decl ~name ~range =
    other_func_decl ~name ~domain:[] ~range
  let get_other_decl_by_name sym =
    Store.(get other_decl_store) sym

  let dim_decl =
    Store.(memoize2 dim_store dim_remapping) @@ fun i ->
    Z3Raw.mk_func_decl ~name:(symbol @@ Format.sprintf "dim#%i" i) ~domain:[] ~range:(sort II)
  let get_dim_decl_by_name sym =
    Store.(get2 dim_store dim_remapping) sym

  let cof_decl =
    Store.(memoize2 cof_store cof_remapping) @@ fun i ->
    Z3Raw.mk_func_decl ~name:(symbol @@ Format.sprintf "cof#%i" i) ~domain:[] ~range:(sort FF)
  let get_cof_decl_by_name sym =
    Store.(get2 cof_store cof_remapping) sym

  let expr =
    let rec loop env e =
      (env, e) |> Store.(memoize expr_store) @@ fun (env, e) ->
      match e with
      | Bound l ->
        let i = Bwd.length env - l - 1 in
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
        let func =
          match sym with
          | `Other sym -> get_other_decl_by_name sym
          | `Dim sym -> get_dim_decl_by_name sym
          | `Cof sym -> get_cof_decl_by_name sym
        in
        let args = List.map (loop env) args in
        Z3Raw.apply func args
    in
    loop Emp

  let pp_sort fmt : Lang.sort -> unit =
    function
    | II -> Uuseg_string.pp_utf_8 fmt "𝕀"
    | FF -> Uuseg_string.pp_utf_8 fmt "𝔽"
    | Real -> Uuseg_string.pp_utf_8 fmt "ℝ"
    | Bool -> Uuseg_string.pp_utf_8 fmt "𝔹"

  let pp_symbol fmt str =
    Format.pp_print_string fmt @@ String.escaped str

  let rec pp_expr fmt =
    let open Lang in
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
      let sym =
        match sym with
        | `Other sym -> sym
        | `Dim sym -> sym
        | `Cof sym -> sym
      in
      Format.fprintf fmt "apply[%a%a]"
        pp_symbol sym
        (fun fmt -> List.iter @@ Format.fprintf fmt ";%a" pp_expr) args

  let rec complexity_expr =
    let open Lang in
    function
    | Bound _l -> 1
    | Ite (e1, e2, e3) -> 1 + complexity_expr e1 + complexity_expr e2 + complexity_expr e3
    | Le (e1, e2) -> 1 + complexity_expr e1 + complexity_expr e2
    | Eq (e1, e2) -> 1 + complexity_expr e1 + complexity_expr e2
    | And es -> List.fold_left (fun c e -> c + complexity_expr e) 1 es
    | RealNumeral _i -> 1
    | Forall (binders, body) -> List.length binders + complexity_expr body
    | Apply (_sym, args) -> List.fold_left (fun c e -> c + complexity_expr e) 1 args
end

module Assertion =
struct
  open Lang
  open Builder

  type t = Lang.expr

  let expr_of_dim =
    let decl x = ignore @@ dim_decl x; Apply (`Dim x, []) in
    let open Dim in
    function
    | Dim0 -> "zero"$[]
    | Dim1 -> "one"$[]
    | DimVar i -> decl @@ Format.sprintf "dim#var[%i]" i
    | DimGlobal sym -> decl @@ Format.sprintf "dim#probe[%s]" (Symbol.show sym)
    | DimProbe sym -> decl @@ Format.sprintf "dim#probe[%s]" (Symbol.show sym)

  let rec expr_of_cof_f : _ -> expr =
    let open Cof in
    function
    | Eq (r1, r2) -> "eq" $[expr_of_dim r1; expr_of_dim r2]
    | Join [] -> "bot"$[]
    | Join (cof::cofs) -> List.fold_left (fun cof1 cof2 -> "lor" $[cof1; expr_of_cof cof2]) (expr_of_cof cof) cofs
    | Meet [] -> "top"$[]
    | Meet (cof::cofs) -> List.fold_left (fun cof1 cof2 -> "land" $[cof1; expr_of_cof cof2]) (expr_of_cof cof) cofs

  and expr_of_cof : CofThyData.cof -> expr =
    let decl x = ignore @@ cof_decl x; Apply (`Cof x, []) in
    let open Cof in
    function
    | Var (`L i) -> "val"$[decl @@ Format.sprintf "cof#var[%i]" i]
    | Var (`G sym) -> "val"$[decl @@ Format.sprintf "cof#global[%s]" (Symbol.show sym)]
    | Cof cof_f -> expr_of_cof_f cof_f

  let of_cof (c : CofThyData.cof) =
    "is-true" $[expr_of_cof c]

  let of_negated_cof (c : CofThyData.cof) =
    "is-false" $[expr_of_cof c]

  let complexity : t -> int = Builder.complexity_expr

  let dump = Builder.pp_expr
end

(* the high-level interface *)
module R = Basis.Monad.MonadReaderResult(struct type local = unit end)
type 'a m = 'a R.m
let bind = R.bind
let ret = R.ret
let throw = R.throw

open Monad.Notation (R)

type check_result = Z3Raw.result =
    UNSATISFIABLE | UNKNOWN | SATISFIABLE

let heyting_solver =
  let open Lang in

  let solver = SolverBuilder.make () in

  (* (define-const bot Real 0.0) *)
  let _ = Builder.other_const_decl ~name:"bot" ~range:Real in
  let () = Z3Raw.add_assertions solver
      [Builder.(expr ("bot"$[] = num 0))]
  in

  (* (define-const top Real 1.0) *)
  let _ = Builder.other_const_decl ~name:"top" ~range:Real in
  let () = Z3Raw.add_assertions solver [Builder.(expr ("top"$[] = num 1))] in

  (* (define-fun in-range ((i Real)) Bool (<= bot i top)) *)
  let _ = Builder.other_func_decl ~name:"in-range" ~domain:[Real] ~range:Bool in
  let () = Z3Raw.add_assertions solver
      [Builder.(expr @@
                forall ["i", Real]
                  ("in-range" $[!%0] = (("bot"$[]) <= !%0 && !%0 <= ("top"$[]))))]
  in

  (* (define-fun land ((i Real) (j Real)) Real (ite (<= i j) i j)) *)
  let _ = Builder.other_func_decl ~name:"land" ~domain:[Real; Real] ~range:Real in
  let () = Z3Raw.add_assertions solver
      [Builder.(expr @@
                forall ["i", Real; "j", Real]
                  ("land"$[!%0; !%1] = (ite (!%0 <= !%1) !%0 !%1)))]
  in

  (* (define-fun lor ((i Real) (j Real)) Real (ite (<= i j) j i)) *)
  let _ = Builder.other_func_decl ~name:"lor" ~domain:[Real; Real] ~range:Real in
  let () = Z3Raw.add_assertions solver
      [Builder.(expr @@
                forall ["i", Real; "j", Real]
                  ("lor" $[!%0; !%1] = (ite (!%0 <= !%1) !%1 !%0)))]
  in

  (* (define-fun arrow ((i Real) (j Real)) Real (ite (<= i j) top j)) *)
  let _ = Builder.other_func_decl ~name:"arrow" ~domain:[Real; Real] ~range:Real in
  let () = Z3Raw.add_assertions solver
      [Builder.(expr @@
                forall ["i", Real; "j", Real]
                  ("arrow" $[!%0; !%1] = ite (!%0 <= !%1) ("top"$[]) !%1))]
  in

  (* (define-fun neg ((i Real)) Real (arrow i bot)) *)
  let _ = Builder.other_func_decl ~name:"neg" ~domain:[Real] ~range:Real in
  let () = Z3Raw.add_assertions solver
      [Builder.(expr @@ forall ["i", Real]
                  ("neg" $[!%0] = ("arrow" $[!%0; "bot"$[]])))]
  in

  (* (define-fun is-true ((i Real)) Bool (= i top)) *)
  let _ = Builder.other_func_decl ~name:"is-true" ~domain:[Real] ~range:Bool in
  let () = Z3Raw.add_assertions solver
      [Builder.(expr @@ forall ["i", Real] ("is-true" $[!%0] = (!%0 = ("top"$[]))))]
  in

  (* (define-fun is-false ((i Real)) Bool (= i bot)) *)
  let _ = Builder.other_func_decl ~name:"is-false" ~domain:[Real] ~range:Bool in
  let () = Z3Raw.add_assertions solver
      [Builder.(expr @@ forall ["i", Real] ("is-false" $[!%0] = (!%0 = ("bot"$[]))))]
  in

  (* (declare-const one I) *)
  let _ = Builder.other_const_decl ~name:"one" ~range:II in

  (* (declare-const zero I) *)
  let _ = Builder.other_const_decl ~name:"zero" ~range:II in

  (* (declare-fun eq (I I) Real) *)
  let _ = Builder.other_func_decl ~name:"eq" ~domain:[II; II] ~range:Real in

  (* (assert (forall ((i I) (j I)) (in-range (eq i j)))) *)
  let () = Z3Raw.add_assertions solver
      [Builder.(expr @@ forall ["i", II; "j", II] ("in-range" $["eq" $[!%0; !%1]]))]
  in

  (* (assert (forall ((i I)) (= (eq i i) top))) *)
  let () = Z3Raw.add_assertions solver
      [Builder.(expr @@ forall ["i", II] ("eq" $[!%0; !%0] = ("top"$[])))]
  in

  (* (assert (forall ((i I) (j I)) (= (eq i j) (eq j i)))) *)
  let () = Z3Raw.add_assertions solver
      [Builder.(expr @@ forall ["i", II; "j", II] (("eq" $[!%0; !%1]) = ("eq" $[!%1; !%0])))]
  in

  (* (assert (forall ((i I) (j I) (k I)) (is-true (arrow (land (eq i j) (eq j k)) (eq i k))))) *)
  let () = Z3Raw.add_assertions solver
      [Builder.(expr @@
                forall ["i", II; "j", II; "k", II]
                  ("is-true" $["arrow" $["land" $["eq" $[!%0; !%1]; "eq" $[!%1; !%2]]; "eq" $[!%0; !%2]]]))]
  in

  (* (assert (is-false (eq one zero))) *)
  let () = Z3Raw.add_assertions solver
      [Builder.(expr ("is-false" $["eq" $["one"$[]; "zero"$[]]]))]
  in

  (* (declare-fun val (F) Real) *)
  let _ = Builder.other_func_decl ~name:"val" ~domain:[FF] ~range:Real in

  (* (assert (forall ((f F)) (in-range (val f)))) *)
  let () = Z3Raw.add_assertions solver
      [Builder.(expr (forall ["f", FF] ("in-range" $["val" $[!%0]])))]
  in

  Store.assert_empty_remappings ();

  (* the base solver with the above theory set up *)
  Z3Raw.push solver;
  solver

let reset () : unit m =
  Z3Raw.pop heyting_solver 1;
  Store.clear_remappings ();
  Z3Raw.push heyting_solver;
  R.ret ()

let run m =
  R.run () m

let run_exn m =
  R.run_exn () m

let () = run_exn (reset ())

let add_cofs cofs =
  R.ret @@ Z3Raw.add_assertions heyting_solver @@
  List.map (fun cof -> Builder.expr (Assertion.of_cof cof)) cofs

let add_negated_cof cof =
  R.ret @@ Z3Raw.add_assertions heyting_solver
    [Builder.expr (Assertion.of_negated_cof cof)]

let check () =
  let ans = Z3Raw.check heyting_solver [] in (* checking with non-empty assumptions seem to be very slow *)
  R.ret ans

let dump_solver () =
  R.ret @@ Z3Raw.dump_solver heyting_solver

let get_reason_unknown () =
  R.ret @@ Z3Raw.get_reason_unknown heyting_solver
