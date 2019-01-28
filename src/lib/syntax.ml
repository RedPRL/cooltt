type uni_level = int
[@@deriving show{ with_path = false }, eq]
type t =
  | Var of int (* DeBruijn indices for variables & ticks *)
  | Let of t * (* BINDS *) t | Check of t * t
  | Nat | Zero | Suc of t | NRec of (* BINDS *) t * t * (* BINDS 2 *) t * t
  | Pi of t * (* BINDS *) t | Lam of (* BINDS *) t | Ap of t * t
  | Sig of t * (* BINDS *) t | Pair of t * t | Fst of t | Snd of t
  | Id of t * t * t | Refl of t | J of (* BINDS 3 *) t * (* BINDS *) t * t
  | Box of t | Open of t | Shut of t
  | Uni of uni_level
[@@deriving eq]

let rec condense = function
  | Zero -> Some 0
  | Suc t ->
    begin
      match condense t with
      | Some n -> Some (n + 1)
      | None -> None
    end
  | _ -> None

let rec pp fmt =
  let open Format in
  function
  | Var i -> fprintf fmt "#%d" i
  | Let (def, body) ->
    fprintf fmt "let@,@[<hov>";
    pp fmt def;
    fprintf fmt "]@,in@,@[<hov>";
    pp fmt body;
    fprintf fmt "@]"
  | Check (term, tp) ->
    fprintf fmt "(@[<hov>";
    pp fmt term;
    fprintf fmt "@]@ :@,[<hov>";
    pp fmt tp;
    fprintf fmt ")@]"
  | Nat -> fprintf fmt "Nat"
  | Zero -> fprintf fmt "0"
  | Suc t ->
    begin
      match condense t with
      | Some n -> fprintf fmt "%d" (n + 1)
      | None ->
        fprintf fmt "suc(@[<hov>";
        pp fmt t;
        fprintf fmt "@])"
    end
  | NRec (mot, zero, suc, n) ->
    fprintf fmt "rec(@[<hov>@[<hov>";
    pp fmt mot;
    fprintf fmt "@],@ @[<hov>";
    pp fmt zero;
    fprintf fmt "@],@ @[<hov>";
    pp fmt suc;
    fprintf fmt "@],@ @[<hov>";
    pp fmt n;
    fprintf fmt "@]@])"
  | Pi (l, r) ->
    fprintf fmt "Pi(@[<hov>@[<hov>";
    pp fmt l;
    fprintf fmt "@],@ @[<hov>";
    pp fmt r;
    fprintf fmt ")@]@]"
  | Lam body ->
    fprintf fmt "lam(@[<hov>";
    pp fmt body;
    fprintf fmt ")@]"
  | Ap (l, r) ->
    fprintf fmt "app(@[<hov>@[<hov>";
    pp fmt l;
    fprintf fmt "@],@ @[<hov>";
    pp fmt r;
    fprintf fmt ")@]@]"
  | Sig (l, r) ->
    fprintf fmt "Sig(@[<hov>@[<hov>";
    pp fmt l;
    fprintf fmt "@],@ @[<hov>";
    pp fmt r;
    fprintf fmt ")@]@]"
  | Fst body ->
    fprintf fmt "fst(@[<hov>";
    pp fmt body;
    fprintf fmt ")@]"
  | Snd body ->
    fprintf fmt "snd(@[<hov>";
    pp fmt body;
    fprintf fmt ")@]"
  | Pair (l, r) ->
    fprintf fmt "pair(@[<hov>@[<hov>";
    pp fmt l;
    fprintf fmt "@],@ @[<hov>";
    pp fmt r;
    fprintf fmt ")@]"
  | Id (tp, l, r) ->
    fprintf fmt "pair(@[<hov>";
    pp fmt tp;
    fprintf fmt "@],@ @[<hov>";
    pp fmt l;
    fprintf fmt "@],@ @[<hov>";
    pp fmt r;
    fprintf fmt ")@]@]"
  | Refl t ->
    fprintf fmt "refl(@[<hov>";
    pp fmt t;
    fprintf fmt ")@]"
  | J (mot, refl, eq) ->
    fprintf fmt "J(@[<hov>@[<hov>";
    pp fmt mot;
    fprintf fmt "@],@ @[<hov>";
    pp fmt refl;
    fprintf fmt "@],@ @[<hov>";
    pp fmt eq;
    fprintf fmt ")@]@]"
  | Box t ->
    fprintf fmt "Box(@[<hov>";
    pp fmt t;
    fprintf fmt ")@]"
  | Shut t ->
    fprintf fmt "shut(@[<hov>";
    pp fmt t;
    fprintf fmt ")@]"
  | Open t ->
    fprintf fmt "open(@[<hov>";
    pp fmt t;
    fprintf fmt ")@]"
  | Uni i -> fprintf fmt "U<%d>" i



let show t =
  let b = Buffer.create 100 in
  let fmt = Format.formatter_of_buffer b in
  pp fmt t;
  Format.pp_print_flush fmt ();
  Buffer.contents b


type env = t list
[@@deriving show { with_path = false }, eq]
