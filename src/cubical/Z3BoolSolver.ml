open Z3Basis

module Lang =
struct
  type sort = II | Bool
  type symbol = string
  type expr =
    | Eq of expr * expr
    | True
    | False
    | And of expr list
    | Or of expr list
    | Not of expr
    | Apply of [`Other of symbol | `Dim of symbol | `Cof of symbol] * expr list

  let (=) e1 e2 = Eq (e1, e2)
  let t = True
  let f = False
  let not e = Not e
  let ($) f args = Apply (`Other f, args)
end

module Store =
struct
  let sort_store : (Lang.sort, Z3Raw.sort) Hashtbl.t = Hashtbl.create 10
  let other_decl_store : (Lang.symbol, Z3Raw.func_decl) Hashtbl.t = Hashtbl.create 10

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
    Hashtbl.clear dim_remapping;
    Hashtbl.clear cof_remapping
end

(* smart builders for various components *)
module Builder =
struct
  let sort =
    Store.(memoize sort_store) @@ function
    | II -> Z3Raw.mk_sort_s "II"
    | Bool -> Z3Raw.mk_bool ()

  let symbol = Z3Raw.mk_symbol_s

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
    Z3Raw.mk_func_decl ~name:(symbol @@ Format.sprintf "cof#%i" i) ~domain:[] ~range:(sort Bool)
  let get_cof_decl_by_name sym =
    Store.(get2 cof_store cof_remapping) sym

  let rec expr =
    let open Lang in
    function
    | Eq (r1, r2) -> Z3Raw.mk_eq (expr r1) (expr r2)
    | True -> Z3Raw.mk_true ()
    | False -> Z3Raw.mk_false ()
    | And es -> Z3Raw.mk_and @@ List.map expr es
    | Or es -> Z3Raw.mk_or @@ List.map expr es
    | Not e -> Z3Raw.mk_not (expr e)
    | Apply (sym, args) ->
      let func =
        match sym with
        | `Other sym -> get_other_decl_by_name sym
        | `Dim sym -> get_dim_decl_by_name sym
        | `Cof sym -> get_cof_decl_by_name sym
      in
      let args = List.map expr args in
      Z3Raw.apply func args

  let pp_sort fmt : Lang.sort -> unit =
    function
    | II -> Uuseg_string.pp_utf_8 fmt "𝕀"
    | Bool -> Uuseg_string.pp_utf_8 fmt "𝔹"

  let pp_symbol fmt str =
    Format.pp_print_string fmt @@ String.escaped str

  let rec pp_expr fmt =
    let open Lang in
    function
    | Eq (e1, e2) -> Format.fprintf fmt "eq[%a;%a]" pp_expr e1 pp_expr e2
    | True -> Format.fprintf fmt "true"
    | False -> Format.fprintf fmt "false"
    | And es ->
      Format.fprintf fmt "and[%a]"
        (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_char fmt ';') pp_expr) es
    | Or es ->
      Format.fprintf fmt "or[%a]"
        (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_char fmt ';') pp_expr) es
    | Not e -> Format.fprintf fmt "not[%a]" pp_expr e
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
    | DimProbe sym -> decl @@ Format.sprintf "dim#probe[%s]" (DimProbe.show sym)

  let rec expr_of_cof_f : _ -> expr =
    let open Cof in
    function
    | Eq (r1, r2) -> expr_of_dim r1 = expr_of_dim r2
    | Join [] -> f
    | Join cofs -> Or (List.map expr_of_cof cofs)
    | Meet [] -> t
    | Meet cofs -> And (List.map expr_of_cof cofs)

  and expr_of_cof : CofThyData.cof -> expr =
    let decl x = ignore @@ cof_decl x; Apply (`Cof x, []) in
    let open Cof in
    function
    | Var i -> decl @@ Format.sprintf "cof#global[%i]" i
    | Cof cof_f -> expr_of_cof_f cof_f

  let of_lhs_cof (c : CofThyData.cof) : t =
    expr_of_cof c

  let of_rhs_cof (c : CofThyData.cof) : t =
    not (expr_of_cof c)

  let dump = Builder.pp_expr
end

type check_result = Z3Raw.result =
    UNSATISFIABLE | UNKNOWN | SATISFIABLE

let solver =
  let open Lang in

  let solver = SolverBuilder.make () in

  (* (declare-const one I) *)
  let _ = Builder.other_const_decl ~name:"one" ~range:II in

  (* (declare-const zero I) *)
  let _ = Builder.other_const_decl ~name:"zero" ~range:II in

  (* (assert (not (= one zero))) *)
  let () = Z3Raw.add_assertions solver
      [Builder.(expr (not (("one"$[]) = ("zero"$[]))))]
  in

  Store.assert_empty_remappings ();

  (* the base solver with the above theory set up *)
  Z3Raw.push solver;
  solver

let add_lhs_cofs cofs =
  Z3Raw.add_assertions solver @@
  List.map (fun cof -> Builder.expr (Assertion.of_lhs_cof cof)) cofs

let add_rhs_cof cof =
  Z3Raw.add_assertions solver
    [Builder.expr (Assertion.of_rhs_cof cof)]

let test_sequent ?rhs ~lhs =
  add_lhs_cofs lhs;
  begin match rhs with None -> () | Some cof -> add_rhs_cof cof end;
  let ans = Z3Raw.check solver [] in (* checking with non-empty assumptions seem to be very slow *)
  Z3Raw.pop solver 1;
  Store.clear_remappings ();
  Z3Raw.push solver;
  ans

let dump_solver () =
  Z3Raw.dump_solver solver

let get_reason_unknown () =
  Z3Raw.get_reason_unknown solver
