%{
  open ConcreteSyntax

  let rec build_join : t list -> t =
    function
    | [] -> BotC
    | [x] -> x
    | (x :: l) -> Join (x, build_join l)

  let rec build_meet : t list -> t =
    function
    | [] -> TopC
    | [x] -> x
    | (x :: l) -> Meet (x, build_meet l)
%}

%token <int> NUMERAL
%token <string> ATOM
%token <string option> HOLE_NAME
%token COLON PIPE AT COMMA RIGHT_ARROW RRIGHT_ARROW UNDERSCORE DIM COF BOUNDARY
%token LPR RPR LBR RBR LSQ RSQ
%token EQUALS JOIN MEET
%token UNIV
%token TIMES FST SND
%token LAM LET IN SUB
%token SUC NAT ZERO UNFOLD
%token PATH
%token COE COM HCOM
%token QUIT NORMALIZE DEF
%token ELIM
%token EOF
%token TOPC BOTC

%start <ConcreteSyntax.signature> sign
%%

name:
  | s = ATOM
    { s }
  | UNDERSCORE
    { "_" }

decl:
  | DEF; nm = name; COLON; tp = term; EQUALS; body = term
    { Def {name = nm; def = body; tp} }
  | QUIT
    { Quit }
  | NORMALIZE; tm = term
    { NormalizeTerm tm }

sign:
  | EOF
    { [] }
  | d = decl; s = sign
    { d :: s }

atomic_cof_except_var:
  | BOUNDARY term = term
    { CofBoundary term }
  | r = atomic_term EQUALS s = atomic_term
    { CofEq (r, s) }

atomic_in_cof: t = atomic_term | t = atomic_cof_except_var {t}

cof_except_var:
  | c = atomic_cof_except_var { c }
  | phi = atomic_in_cof JOIN psis = separated_nonempty_list(JOIN, atomic_in_cof)
    { build_join (phi :: psis) }
  | phi = atomic_in_cof MEET psis = separated_nonempty_list(MEET, atomic_in_cof)
    { build_meet (phi :: psis) }

cof_or_atomic_term: t = atomic_term | t = cof_except_var {t}
cof_or_term: t = term | t = cof_except_var {t}

atomic_term:
  | LBR term = cof_or_term RBR
    { term }
  | a = ATOM
    { Var (`User a) }
  | ZERO
    { Lit 0 }
  | n = NUMERAL
    { Lit n }
  | NAT
    { Nat }
  | UNIV
    { Univ }
  | name = HOLE_NAME
    { Hole name }
  | UNDERSCORE
    { Underscore }
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
  | cases = separated_list(PIPE, cof_case)
    { CofSplit cases }
  | PIPE cases = separated_list(PIPE, cof_case)
    { CofSplit cases }
  | t = cof_or_term
    { Prf t }

app_term:
  | t = atomic_term { t }
  | f = atomic_term; args = nonempty_list(atomic_term)
    { Ap (f, args) }

term:
  | t = app_term
    { t }
  | UNFOLD; names = nonempty_list(name); IN; body = term;
    { Unfold (names, body) }
  | LET; name = name; COLON; tp = term; EQUALS; def = term; IN; body = term
    { Let (Ann {term = def; tp}, B {name; body}) }
  | LET; name = name; EQUALS; def = term; IN; body = term
    { Let (def, B {name; body}) }
  | LPR t = term; AT; tp = term RPR
    { Ann {term = t; tp} }
  | SUC; t = term
    { Suc t }
  | LAM; names = list(name); RRIGHT_ARROW; body = term
    { Lam (BN {names; body}) }
  | LAM; ELIM; cases = cases
    { LamElim cases }
  | ELIM; scrut = term; AT; mot = motive; cases = cases
    { Elim {mot; cases; scrut}}
  | tele = nonempty_list(tele_cell); RIGHT_ARROW; cod = term
    { Pi (tele, cod) }
  | tele = nonempty_list(tele_cell); TIMES; cod = term
    { Sg (tele, cod) }
  | dom = app_term RIGHT_ARROW cod = term
    { Pi ([Cell {name = "_"; tp = dom}], cod) }
  | dom = app_term TIMES cod = term
    { Sg ([Cell {name = "_"; tp = dom}], cod) }
  | SUB tp = atomic_term phi = atomic_term tm = atomic_term
    { Sub (tp, phi, tm) }
  | FST; t = term
    { Fst t }
  | SND; t = term
    { Snd t }

  | PATH; tp = atomic_term; left = atomic_term; right = atomic_term
    { Path (tp, left, right) }

  | COE; fam = atomic_term; src = atomic_term; trg = atomic_term; body = atomic_term
    { Coe (fam, src, trg, body) }
  | HCOM; tp = atomic_term; src = atomic_term; trg = atomic_term; phi = atomic_term; body = atomic_term
    { HCom (tp, src, trg, phi, body) }
  | HCOM; tp = atomic_term; src = atomic_term; trg = atomic_term; body = atomic_term
    { AutoHCom (tp, src, trg, body) }
  | COM; fam = atomic_term; src = atomic_term; trg = atomic_term; phi = atomic_term; body = atomic_term
    { Com (fam, src, trg, phi, body) }

motive:
  | LBR names = list(name) RRIGHT_ARROW body = term RBR
    { BN {names; body} }

cases:
  | LSQ option(PIPE) cases = separated_list(PIPE, case) RSQ
    { cases }

case:
  | p = pat RRIGHT_ARROW t = term
    { p, t }

cof_case:
  | phi = cof_or_atomic_term RRIGHT_ARROW t = term
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
  | ident = name
    { `Simple (Some ident) }
  | LBR i0 = name RRIGHT_ARROW i1 = name RBR
    { `Inductive (Some i0, Some i1) }

tele_cell:
  | LPR name = name; COLON tp = term; RPR
    { Cell {name; tp} }
