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
  let mk_symbol_i i = Z3.Symbol.mk_int context i

  type sort = Z3.Sort.sort
  let mk_sort_s s = Z3.Sort.mk_uninterpreted_s context s
  let mk_real () = Z3.Arithmetic.Real.mk_sort context

  type expr = Z3.Expr.expr
  let mk_const sym sort = Z3.Expr.mk_const context sym sort
  let mk_ite e1 e2 e3 = Z3.Boolean.mk_ite context e1 e2 e3
  let mk_le e1 e2 = Z3.Arithmetic.mk_le context e1 e2
  let mk_eq e1 e2 = Z3.Boolean.mk_eq context e1 e2
  let mk_real_numeral_i i = Z3.Arithmetic.Real.mk_numeral_i context i

  type quantifier = Z3.Quantifier.quantifier
  let mk_bound i sort = Z3.Quantifier.mk_bound context i sort
  let expr_of_quantifier = Z3.Quantifier.expr_of_quantifier
  let mk_forall ~sort ~symbol ~body : quantifier =
    Z3.Quantifier.mk_forall context [sort] [symbol] body None [] [] None None

  type func_decl = Z3.FuncDecl.func_decl
  let mk_func_decl ~name ~domain ~range : func_decl =
    Z3.FuncDecl.mk_func_decl context name domain range
  let apply func args = Z3.FuncDecl.apply func args
end

(* smart builder for various components *)
module Z3Builder =
struct
  type sort = I | F | Real
  type symbol = string
  type expr =
    | Bound of int * sort (* de Bruijn indexes *)
    | Var of symbol * sort
    | Ite of expr * expr * expr
    | Le of expr * expr
    | Eq of expr * expr
    | RealConst of int
    | ForallI of symbol * expr
    | Apply of symbol * expr list

  let memoize store f x =
    match Hashtbl.find_opt store x with
    | Some x -> x
    | None -> let res = f x in Hashtbl.replace store x res; res

  let sort_store : (sort, Z3Raw.sort) Hashtbl.t = Hashtbl.create 10
  let sort =
    memoize sort_store @@ function
    | I -> Z3Raw.mk_sort_s "I"
    | F -> Z3Raw.mk_sort_s "F"
    | Real -> Z3Raw.mk_real ()

  let new_symbol str = Z3Raw.mk_symbol_s str

  let global_symbol_store : (symbol, Z3Raw.symbol) Hashtbl.t = Hashtbl.create 100
  let global_symbol = memoize global_symbol_store @@ new_symbol

  let func_decl_store : (symbol, Z3Raw.func_decl) Hashtbl.t = Hashtbl.create 10
  let func_decl ~name ~domain ~range =
    name |> begin
      memoize func_decl_store @@ fun name ->
      let name = new_symbol name in
      let domain = List.map sort domain in
      let range = sort range in
      Z3Raw.mk_func_decl ~name ~domain ~range
    end

  let get_func_decl_by_name sym =
    Hashtbl.find func_decl_store sym

  let expr_store : (expr, Z3Raw.expr) Hashtbl.t = Hashtbl.create 100
  let rec expr e =
    e |> memoize expr_store @@ function
    | Bound (i, s) -> Z3Raw.mk_bound i (sort s)
    | Var (sym, s) -> Z3Raw.mk_const (global_symbol sym) (sort s)
    | Ite (e1, e2, e3) -> Z3Raw.mk_ite (expr e1) (expr e2) (expr e3)
    | Le (e1, e2) -> Z3Raw.mk_le (expr e1) (expr e2)
    | Eq (e1, e2) -> Z3Raw.mk_eq (expr e1) (expr e2)
    | RealConst i -> Z3Raw.mk_real_numeral_i i
    | ForallI (sym, body) ->
      let symbol = new_symbol sym in
      let sort = sort I in
      let body = expr body in
      Z3Raw.expr_of_quantifier @@ Z3Raw.mk_forall ~sort ~symbol ~body
    | Apply (sym, args) ->
      let func = get_func_decl_by_name sym in
      let args = List.map expr args in
      Z3Raw.apply func args

  let pp_sort fmt : sort -> unit =
    function
    | I -> Uuseg_string.pp_utf_8 fmt "𝕀"
    | F -> Uuseg_string.pp_utf_8 fmt "𝔽"
    | Real -> Uuseg_string.pp_utf_8 fmt "ℝ"

  let pp_symbol fmt str =
    Format.pp_print_string fmt @@ String.escaped str

  let rec pp_expr fmt =
    function
    | Bound (i, s) -> Format.fprintf fmt "bound[%i;%a]" i pp_sort s
    | Var (sym, s) -> Format.fprintf fmt "var[%a;%a]" pp_symbol sym pp_sort s
    | Ite (e1, e2, e3) -> Format.fprintf fmt "ite[%a;%a;%a]" pp_expr e1 pp_expr e2 pp_expr e3
    | Le (e1, e2) -> Format.fprintf fmt "le[%a;%a]" pp_expr e1 pp_expr e2
    | Eq (e1, e2) -> Format.fprintf fmt "eq[%a;%a]" pp_expr e1 pp_expr e2
    | RealConst i -> Format.fprintf fmt "real[%i]" i
    | ForallI (sym, body) -> Format.fprintf fmt "forall_i[%a;%a]" pp_symbol sym pp_expr body
    | Apply (sym, args) ->
      Format.fprintf fmt "apply[%a%a]"
        pp_symbol sym
        (fun fmt args -> List.iter (Format.fprintf fmt ";%a" pp_expr) args) args
end
