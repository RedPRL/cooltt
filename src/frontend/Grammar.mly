%{
  open Core
  open ConcreteSyntax

  let locate (start, stop) node =
    {node; info = Some {start; stop}}

  let name_of_atoms parts = `User parts

  let name_of_underscore = `Anon

  let plain_term_of_name =
    function
    | `User a -> Var (`User a)
    | `Anon -> Underscore
    | `Machine _ -> failwith "Impossible Internal Error"

  let term_of_name {node; info} =
    {node = plain_term_of_name node; info}

  let drop_location {node; info = _} = node

  let ap_or_atomic f =
    function
    | [] -> drop_location f
    | args -> Ap (f, args)
%}

%token <int> NUMERAL
%token <string> ATOM
%token <string option> HOLE_NAME
%token LOCKED UNLOCK
%token BANG COLON COLON_EQUALS PIPE COMMA DOT SEMI RIGHT_ARROW RRIGHT_ARROW UNDERSCORE DIM COF BOUNDARY LVL
%token LPR RPR LBR RBR LSQ RSQ
%token EQUALS JOIN MEET
%token TYPE
%token TIMES FST SND
%token LET IN SUB
%token SUC NAT ZERO UNFOLD GENERALIZE WITH
%token CIRCLE BASE LOOP
%token EXT
%token COE COM HCOM HFILL
%token QUIT NORMALIZE PRINT DEF AXIOM
%token <string list> IMPORT
%token ELIM
%token SEMISEMI EOF
%token TOPC BOTC
%token V VPROJ CAP

%nonassoc IN RRIGHT_ARROW
%nonassoc COLON
%right SEMI
%nonassoc SUC LOOP RIGHT_ARROW TIMES

%start <ConcreteSyntax.signature> sign
%start <ConcreteSyntax.command> command
%type <Ident.t> plain_name
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

reversed_list_left_recursive(X):
  | {[]}
  | xs = reversed_list_left_recursive(X) x = X {x::xs}

%inline list_left_recursive(X):
  | xs = rev(reversed_list_left_recursive(X)) {xs}

reversed_nonempty_list_left_recursive(X):
  | x = X {[x]}
  | xs = reversed_nonempty_list_left_recursive(X) x = X {x::xs}

%inline nonempty_list_left_recursive(X):
  | xs = rev(reversed_nonempty_list_left_recursive(X)) {xs}

reversed_separated_list_left_recursive(S,X):
  | {[]}
  | xs = reversed_separated_list_left_recursive(S,X) S x = X {x::xs}

%inline separated_list_left_recursive(S,X):
  | xs = rev(reversed_separated_list_left_recursive(S,X)) {xs}

reversed_separated_nonempty_list_left_recursive(S,X):
  | x = X {[x]}
  | xs = reversed_separated_nonempty_list_left_recursive(S,X) S x = X {x::xs}

%inline separated_nonempty_list_left_recursive(S,X):
  | xs = rev(reversed_separated_nonempty_list_left_recursive(S,X)) {xs}

term: t = located(plain_term) {t}
atomic_in_cof: t = located(plain_atomic_in_cof) {t}
%inline
name: t = located(plain_name) {t}
bracketed_modifier: t = located(plain_bracketed_modifier) {t}
modifier: t = located(plain_modifier) {t}
atomic_term_except_name: t = located(plain_atomic_term_except_name) {t}
atomic_term: t = located(plain_atomic_term) {t}
spine: t = located(plain_spine) {t}

%inline path:
  | path = separated_nonempty_list_left_recursive(DOT, ATOM)
    { path }

plain_name:
  | path = path
    { name_of_atoms path }
  | UNDERSCORE
    { name_of_underscore }

decl:
  | DEF; nm = plain_name; tele = list(tele_cell); COLON; tp = term; COLON_EQUALS; body = term
    { Def {name = nm; args = tele; def = Some body; tp} }
  | AXIOM; nm = plain_name; tele = list(tele_cell); COLON; tp = term
    { Def {name = nm; args = tele; def = None; tp} }
  | QUIT
    { Quit }
  | NORMALIZE; tm = term
    { NormalizeTerm tm }
  | unitpath = IMPORT; m = ioption(bracketed_modifier)
    { Import (unitpath, m) }
  | PRINT; name = name
    { Print name }

sign:
  | EOF
    { [] }
  | SEMISEMI; s = sign
    { s }
  | d = decl; s = sign
    { d :: s }

command:
  | EOF
    { EndOfFile }
  | SEMISEMI
    { NoOp }
  | d = decl; SEMISEMI
    { Decl d }

plain_bracketed_modifier:
  | LSQ list = separated_list(SEMI, modifier) RSQ
    { ModSeq list }
  | LBR list = separated_list(COMMA, modifier) RBR
    { ModUnion list }

plain_modifier:
  | m = plain_bracketed_modifier
    { m }
  | path = path DOT m = bracketed_modifier
    { ModInSubtree (path, m) }
  | RIGHT_ARROW
    { ModRename ([], []) }
  | path = path RIGHT_ARROW ioption(DOT)
    { ModRename (path, []) }
  | ioption(DOT) RIGHT_ARROW path = path
    { ModRename ([], path) }
  | path1 = path RIGHT_ARROW path2 = path
    { ModRename (path1, path2) }
  | path = path
    { ModOnly path }
  | BANG ioption(DOT)
    { ModNone }
  | BANG path = path
    { ModExcept path }
  | name = HOLE_NAME
    { ModPrint name }

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
  | BASE
    { Base }
  | CIRCLE
    { Circle }
  | name = HOLE_NAME
    { Hole (name, None) }
  | DIM
    { Dim }
  | LVL
    { Lvl }
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
    { plain_term_of_name name }
  | t = plain_atomic_term_except_name
    { t }

plain_spine:
  | spine = nonempty_list_left_recursive(name); arg = atomic_term_except_name; args = list(atomic_term)
    { Ap (term_of_name (List.hd spine), List.concat [List.map term_of_name (List.tl spine); [arg]; args]) }
  | spine = nonempty_list_left_recursive(name)
    { ap_or_atomic (term_of_name (List.hd spine)) (List.map term_of_name (List.tl spine)) }
  | f = atomic_term_except_name; args = list(atomic_term)
    { ap_or_atomic f args }

plain_lambda_and_cof_case:
  | name = name; RRIGHT_ARROW; body = term
    { name, body }

plain_lambda_except_cof_case:
  | names1 = nonempty_list_left_recursive(name); name2 = plain_name; RRIGHT_ARROW; body = term
  { Lam (List.map drop_location names1 @ [name2], body) }

plain_term:
  | t = plain_lambda_and_cof_case
    { let name, body = t in Lam ([drop_location name], body)  }
  | t = plain_term_except_cof_case
    { t }

plain_term_except_cof_case:
  | t = plain_spine
    { t }
  | UNLOCK; t = term; IN; body = term;
    { Unlock (t, body) }
  | UNFOLD; names = nonempty_list(plain_name); IN; body = term;
    { Unfold (names, body) }
  | GENERALIZE; name = plain_name; IN; body = term;
    { Generalize (name, body) }
  | LET; name = plain_name; COLON; tp = term; COLON_EQUALS; def = term; IN; body = term
    { Let ({node = Ann {term = def; tp}; info = def.info}, name, body) }
  | LET; name = plain_name; COLON_EQUALS; def = term; IN; body = term
    { Let (def, name, body) }
  | t = term; COLON; tp = term
    { Ann {term = t; tp} }
  | LOCKED; phi = atomic_term
    { Locked phi }
  | TYPE; c = atomic_term
    { Type c }
  | SUC; t = term
    { Suc t }
  | LOOP; t = term
    { Loop t }
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
  | FST; t = atomic_term
    { Fst t }
  | SND; t = atomic_term
    { Snd t }
  | V; r = atomic_term; a = atomic_term; b = atomic_term; e = atomic_term
    { V (r, a, b, e) }
  | VPROJ; t = atomic_term
    { VProj t }
  | CAP; t = atomic_term
    { Cap t }
  | name = HOLE_NAME; SEMI; t = term
    { Hole (name, Some t) }

  | EXT; names = list(plain_name); RRIGHT_ARROW; fam = term; WITH; LSQ; ioption(PIPE) cases = separated_list(PIPE, cof_case); RSQ;
    { Ext (names, fam, cases) }

  | COE; fam = atomic_term; src = atomic_term; trg = atomic_term; body = atomic_term
    { Coe (fam, src, trg, body) }
  | HCOM; tp = atomic_term; src = atomic_term; trg = atomic_term; phi = atomic_term; body = atomic_term
    { HCom (tp, src, trg, phi, body) }
  | HFILL; tp = atomic_term; src = atomic_term; phi = atomic_term; body = atomic_term
    { HFill (tp, src, phi, body) }
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
    { let name, body = t in term_of_name name, body }
  | phi = located(plain_cof_or_atomic_term_except_name) RRIGHT_ARROW t = term
    { phi, t }

pat_lbl:
  | ZERO
    { "zero" }
  | SUC
    { "suc" }
  | BASE
    { "base" }
  | LOOP
    { "loop" }
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
