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
  let mk_true () = Z3.Boolean.mk_true context
  let mk_false () = Z3.Boolean.mk_false context
  let mk_not e = Z3.Boolean.mk_not context e
  let mk_and es = Z3.Boolean.mk_and context es
  let mk_or es = Z3.Boolean.mk_or context es
  let mk_implies e1 e2 = Z3.Boolean.mk_implies context e1 e2
  let mk_eq e1 e2 = Z3.Boolean.mk_eq context e1 e2
  let mk_ite e1 e2 e3 = Z3.Boolean.mk_ite context e1 e2 e3
  let mk_le e1 e2 = Z3.Arithmetic.mk_le context e1 e2
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

module SolverBuilder =
struct
  let make () =
    let solver = Z3Raw.mk_solver () in
    let params = Z3Raw.mk_params () in
    Z3Raw.add_int_param params (Z3Raw.mk_symbol_s "solver2_timeout") 10;
    Z3Raw.set_parameters solver params;
    solver
end
