%{
  open ConcreteSyntax

  let locate (start, stop) node =
    {node; info = Some {start; stop}}

  let atom_as_name a = `User a

  let underscore_as_name = `Anon

  let plain_name_to_term =
    function
    | `User a -> Var (`User a)
    | `Anon -> Underscore
    | `Machine _ -> failwith "Impossible Internal Error"

  let name_to_term {node; info} =
    {node = plain_name_to_term node; info}

  let forget_location {node; info} = node

  let rec rev_ann' tp term = {node = Ann {term; tp}; info = term.info}

  let rec rev_ann rev_tps term =
    List.fold_right rev_ann' rev_tps term
%}

%token <int> NUMERAL
%token <string> ATOM
%token <string option> HOLE_NAME
%token COLON PIPE COMMA RIGHT_ARROW RRIGHT_ARROW UNDERSCORE DIM COF BOUNDARY
%token LPR RPR LBR RBR LSQ RSQ
%token EQUALS JOIN MEET
%token TYPE
%token TIMES FST SND
%token LET IN SUB
%token SUC NAT ZERO UNFOLD
%token PATHD
%token COE COM HCOM HFILL
%token QUIT NORMALIZE PRINT DEF
%token ELIM
%token EOF
%token TOPC BOTC

%nonassoc IN RRIGHT_ARROW
%left COLON
%nonassoc FST SND SUC RIGHT_ARROW TIMES

%start <ConcreteSyntax.signature> sign
%type <Ident.t> plain_name name
%type <con_>
  plain_atomic_in_cof_except_term
  plain_cof_except_term
  plain_atomic_term_except_name
  bracketed
  plain_spine
  plain_lambda_except_cof_case
  plain_term_except_cof_case
%type <pat> pat
%type <pat * con> case
%type <con * con> cof_case
%type <cell> tele_cell
%%

%inline
located(X):
  | e = X
    { locate $loc e }

term: t = located(plain_term) {t}
atomic_in_cof: t = located(plain_atomic_in_cof) {t}
%inline
name: t = located(plain_name) {t}
atomic_term_except_name: t = located(plain_atomic_term_except_name) {t}
atomic_term: t = located(plain_atomic_term) {t}
spine: t = located(plain_spine) {t}

plain_name:
  | s = ATOM
    { atom_as_name s }
  | UNDERSCORE
    { underscore_as_name }

decl:
  | DEF; nm = plain_name; COLON; tp = term; EQUALS; body = term
    { Def {name = nm; def = body; tp} }
  | QUIT
    { Quit }
  | NORMALIZE; tm = term
    { NormalizeTerm tm }
  | PRINT; name = name
    { Print name }

sign:
  | EOF
    { [] }
  | d = decl; s = sign
    { d :: s }

plain_atomic_in_cof_except_term:
  | BOUNDARY t = atomic_term
    { CofBoundary t }
  | r = atomic_term EQUALS s = atomic_term
    { CofEq (r, s) }

plain_atomic_in_cof:
  | t = plain_atomic_term
  | t = plain_atomic_in_cof_except_term
    { t }

plain_cof_except_term:
  | c = plain_atomic_in_cof_except_term
    { c }
  | phi = atomic_in_cof JOIN psis = separated_nonempty_list(JOIN, atomic_in_cof)
    { Join (phi :: psis) }
  | phi = atomic_in_cof MEET psis = separated_nonempty_list(MEET, atomic_in_cof)
    { Meet (phi :: psis) }

plain_cof_or_atomic_term_except_name:
  | t = plain_atomic_term_except_name
  | t = plain_cof_except_term
    { t }
plain_cof_or_term_except_cof_case:
  | t = plain_term_except_cof_case
  | t = plain_cof_except_term
    { t }
plain_cof_or_term:
  | t = plain_term
  | t = plain_cof_except_term
    { t }

plain_atomic_term_except_name:
  | LBR t = plain_cof_or_term RBR
    { t }
  | ZERO
    { Lit 0 }
  | n = NUMERAL
    { Lit n }
  | NAT
    { Nat }
  | TYPE
    { Type }
  | name = HOLE_NAME
    { Hole name }
  | DIM
    { Dim }
  | COF
    { Cof }
  | TOPC
    { TopC }
  | BOTC
    { BotC }

  | LSQ t = bracketed RSQ
    { t }

bracketed:
  | left = term COMMA right = term
    { Pair (left, right) }
  | ioption(PIPE) cases = separated_list(PIPE, cof_case)
    { CofSplit cases }
  | t = located(plain_cof_or_term_except_cof_case)
    { Prf t }

plain_atomic_term:
  | name = plain_name
    { plain_name_to_term name }
  | t = plain_atomic_term_except_name
    { t }

plain_spine:
  | spine = nonempty_list(name); arg = atomic_term_except_name; args = list(atomic_term)
    { Ap (name_to_term (List.hd spine), List.map name_to_term (List.tl spine) @ [arg] @ args) }
  | f = atomic_term_except_name; args = nonempty_list(atomic_term)
    { Ap (f, args) }
  | f = name; args = nonempty_list(name)
    { Ap (name_to_term f, List.map name_to_term args) }
  | t = plain_atomic_term
    { t }

plain_lambda_and_cof_case:
  | name = name; RRIGHT_ARROW; body = term
    { name, body }

plain_lambda_except_cof_case:
  | name1 = name; names2 = nonempty_list(plain_name); RRIGHT_ARROW; body = term
    { Lam (forget_location name1 :: names2, body) }

plain_term:
  | t = plain_lambda_and_cof_case
    { let name, body = t in Lam ([forget_location name], body)  }
  | t = plain_term_except_cof_case
    { t }

rev_annotated(X):
  | t = X
    {t, []}
  | ann = rev_annotated(X); COLON; tp = term
    { let t, tps = ann in t, tp :: tps }

plain_term_except_cof_case:
  | t = plain_spine
    { t }
  | UNFOLD; names = nonempty_list(plain_name); IN; body = term;
    { Unfold (names, body) }
  | LET; rev_annotated_name = rev_annotated(plain_name); EQUALS; def = term; IN; body = term
    { let name, rev_tps = rev_annotated_name in
      Let (rev_ann rev_tps def, name, body) }
  | t = term; COLON; tp = term
    { Ann {term = t; tp} }
  | SUC; t = term
    { Suc t }
  | t = plain_lambda_except_cof_case
    { t }
  | ELIM; cases = cases
    { LamElim cases }
  | tele = nonempty_list(tele_cell); RIGHT_ARROW; cod = term
    { Pi (tele, cod) }
  | tele = nonempty_list(tele_cell); TIMES; cod = term
    { Sg (tele, cod) }
  | dom = spine; RIGHT_ARROW; cod = term
    { Pi ([Cell {name = `Anon; tp = dom}], cod) }
  | dom = spine; TIMES; cod = term
    { Sg ([Cell {name = `Anon; tp = dom}], cod) }
  | SUB; tp = atomic_term; phi = atomic_term; tm = atomic_term
    { Sub (tp, phi, tm) }
  | FST; t = term
    { Fst t }
  | SND; t = term
    { Snd t }

  | PATHD; tp = atomic_term; left = atomic_term; right = atomic_term
    { Path (tp, left, right) }

  | COE; fam = atomic_term; src = atomic_term; trg = atomic_term; body = atomic_term
    { Coe (fam, src, trg, body) }
  | HCOM; tp = atomic_term; src = atomic_term; trg = atomic_term; phi = atomic_term; body = atomic_term
    { HCom (tp, src, trg, phi, body) }
  | HFILL; tp = atomic_term; src = atomic_term; phi = atomic_term; body = atomic_term
    { HFill (tp, src, phi, body) }
  | HCOM; tp = atomic_term; src = atomic_term; trg = atomic_term; body = atomic_term
    { AutoHCom (tp, src, trg, body) }
  | COM; fam = atomic_term; src = atomic_term; trg = atomic_term; phi = atomic_term; body = atomic_term
    { Com (fam, src, trg, phi, body) }

cases:
  | LSQ option(PIPE) cases = separated_list(PIPE, case) RSQ
    { cases }

case:
  | p = pat RRIGHT_ARROW t = term
    { p, t }

cof_case:
  | t = plain_lambda_and_cof_case
    { let name, body = t in name_to_term name, body }
  | phi = located(plain_cof_or_atomic_term_except_name) RRIGHT_ARROW t = term
    { phi, t }

pat_lbl:
  | ZERO
    { "zero" }
  | SUC
    { "suc" }
  | lbl = ATOM
    { lbl }


pat:
  | lbl = pat_lbl args = list(pat_arg)
   { Pat {lbl; args} }

pat_arg:
  | ident = plain_name
    { `Simple ident }
  | LBR i0 = plain_name RRIGHT_ARROW i1 = plain_name RBR
    { `Inductive (i0, i1) }

tele_cell:
  | LPR name = plain_name; COLON tp = term; RPR
    { Cell {name; tp} }
