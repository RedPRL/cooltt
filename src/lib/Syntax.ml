type t =
  | Var of int (* DeBruijn indices for variables *)
  | Global of Symbol.t
  | Let of t * (* BINDS *) t
  | Check of t * tp
  | Zero
  | Suc of t
  | NRec of (* BINDS *) tp * t * (* BINDS 2 *) t * t
  | Lam of (* BINDS *) t
  | Ap of t * t
  | Pair of t * t
  | Fst of t
  | Snd of t
  | Refl of t
  | J of (* BINDS 3 *) tp * (* BINDS *) t * t

and tp =
  | Nat
  | Pi of tp * (* BINDS *) tp
  | Sg of tp * (* BINDS *) tp
  | Id of tp * t * t

let rec condense = function
  | Zero -> Some 0
  | Suc t -> (
      match condense t with
      | Some n -> Some (n + 1)
      | None -> None )
  | _ -> None

let rec pp fmt =
  let open Format in
  function
  | Var i -> fprintf fmt "#%d" i
  | Global sym -> fprintf fmt "%a" Symbol.pp sym
  | Let (def, body) ->
    fprintf fmt "let@,@[<hov>%a@]@,in@,@[<hov%a@]" pp def pp body
  | Check (term, tp) ->
    fprintf fmt "(@[<hov>%a@]@ :@,@[<hov>%a@])" pp term pp_tp tp
  | Zero -> fprintf fmt "0"
  | Suc t -> (
      match condense t with
      | Some n -> fprintf fmt "%d" (n + 1)
      | None -> fprintf fmt "suc(@[<hov>%a@])" pp t )
  | NRec (mot, zero, suc, n) ->
    fprintf fmt
      "rec(@[<hov>@[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@]@])"
      pp_tp mot pp zero pp suc pp n
  | Lam body -> fprintf fmt "lam(@[<hov>%a@])" pp body
  | Ap (l, r) ->
    fprintf fmt "app(@[<hov>@[<hov>%a@],@ @[<hov>%a@]@])" pp l pp r
  | Fst body -> fprintf fmt "fst(@[<hov>%a@])" pp body
  | Snd body -> fprintf fmt "snd(@[<hov>%a@])" pp body
  | Pair (l, r) ->
    fprintf fmt "pair(@[<hov>@[<hov>%a@],@ @[<hov>%a@]@])" pp l pp r
  | Refl t -> fprintf fmt "refl(@[<hov>%a@])" pp t
  | J (mot, refl, eq) ->
    fprintf fmt "J(@[<hov>@[<hov>%a@],@ @[<hov>%a@]@, @[<hov>%a@]@])" pp_tp
      mot pp refl pp eq

and pp_tp fmt =
  let open Format in
  function
  | Nat -> fprintf fmt "Nat"
  | Pi (l, r) ->
    fprintf fmt "Pi(@[<hov>@[<hov>%a@],@ @[<hov>%a@]@])" pp_tp l pp_tp r
  | Sg (l, r) ->
    fprintf fmt "Sg(@[<hov>@[<hov>%a@],@ @[<hov>%a@]@])" pp_tp l pp_tp r
  | Id (tp, l, r) ->
    fprintf fmt "Id(@[<hov>@[<hov>%a@],@ @[<hov>%a@],@ @[<hov>%a@]@])" pp_tp
      tp pp l pp r

type env = tp list