%{
  open Core
  open ConcreteSyntax

  let locate (start, stop) node =
    {node; info = Some {start; stop}}

  let info_at (start, stop) : info =
    Some {start; stop}

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

  let ap_or_atomic =
    function
    | [] -> failwith "Impossible Internal Error"
    | [f] -> drop_location f
    | f :: args -> Ap (f, args)
%}

%token <int> NUMERAL
%token <string> ATOM
%token <string option> HOLE_NAME
%token LOCKED UNLOCK
%token BANG COLON COLON_COLON COLON_EQUALS HASH PIPE COMMA DOT DOT_EQUALS SEMI RIGHT_ARROW RRIGHT_ARROW UNDERSCORE DIM COF BOUNDARY
%token LPR RPR LBR RBR LSQ RSQ LBANG RBANG
%token EQUALS JOIN MEET
%token TYPE
%token TIMES FST SND
%token LET IN SUB
%token SUC NAT ZERO UNFOLD GENERALIZE WITH
%token CIRCLE BASE LOOP
%token SIG STRUCT AS
%token EXT
%token COE COM HCOM HFILL
%token QUIT NORMALIZE PRINT DEF AXIOM FAIL
%token <string list> IMPORT
%token ELIM
%token SEMISEMI EOF
%token TOPC BOTC
%token V VPROJ CAP
%token BEGIN EQUATION END LSQEQUALS LRSQEQUALS
%token SECTION VIEW EXPORT REPACK

%nonassoc IN AS RRIGHT_ARROW SEMI
%nonassoc COLON
%left DOT
%right RIGHT_ARROW TIMES
%nonassoc HASH

%start <ConcreteSyntax.signature> sign
%start <ConcreteSyntax.command> command
%type <Ident.t> plain_name
%type <con_>
  plain_atomic_in_cof_except_term
  plain_cof_except_term
  plain_atomic_term_except_name
  bracketed
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
atomic_modifier: t = located(plain_atomic_modifier) {t}
modifier: t = located(plain_modifier) {t}
atomic_term_except_sq: t = located(plain_atomic_term_except_sq) {t}
atomic_term_except_name: t = located(plain_atomic_term_except_name) {t}
atomic_term: t = located(plain_atomic_term) {t}

%inline path:
  | path = separated_nonempty_list_left_recursive(COLON_COLON, ATOM)
    { path }

%inline iocc_path: /* iocc = ioption(COLON_COLON) */
  | ioption(COLON_COLON) path = path
    { path }

user:
  | path = path
    { `User path }

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
  | FAIL; nm = plain_name; tele = list(tele_cell); COLON; tp = term; COLON_EQUALS; body = term
    { Fail {name = nm; args = tele; def = body; tp; info = info_at $loc} }
  | QUIT
    { Quit }
  | NORMALIZE; tm = term
    { NormalizeTerm tm }
  | shadowing = boption(BANG); unitpath = IMPORT; modifier = ioption(bracketed_modifier)
    { Import {shadowing; unitpath; modifier} }
  | PRINT; name = name
    { Print name }
  | shadowing = boption(BANG); VIEW; modifier = bracketed_modifier
    { View {shadowing; modifier} }
  | shadowing = boption(BANG); EXPORT; modifier = bracketed_modifier
    { Export {shadowing; modifier} }
  | shadowing = boption(BANG); EXPORT; path = located(path)
    { Export {shadowing; modifier = map_node ~f:(fun p -> ModOnly p) path } }
  | shadowing = boption(BANG); REPACK; modifier = bracketed_modifier
    { Repack {shadowing; modifier} }
  | shadowing = boption(BANG); SECTION; prefix = ioption(path); BEGIN; decls = list(decl); END; modifier = ioption(bracketed_modifier)
    { Section {shadowing; prefix; decls; modifier} }

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

plain_atomic_modifier:
  | m = plain_bracketed_modifier { m }
  | BANG ioption(COLON_COLON)
    { ModNone }
  | BANG path = iocc_path
    { ModExcept path }
  | name = HOLE_NAME
    { ModPrint name }

plain_modifier:
  | COLON_COLON
    { ModAny }
  | path = iocc_path COLON_COLON m = atomic_modifier
    { ModInSubtree (path, m) }
  | RIGHT_ARROW
    { ModRename ([], []) }
  | path = iocc_path RIGHT_ARROW ioption(COLON_COLON)
    { ModRename (path, []) }
  | ioption(COLON_COLON) RIGHT_ARROW path = iocc_path
    { ModRename ([], path) }
  | path1 = iocc_path RIGHT_ARROW path2 = iocc_path
    { ModRename (path1, path2) }
  | path = iocc_path
    { ModOnly path }
  | m = plain_atomic_modifier
    { m }

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

plain_atomic_term_except_sq:
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
  | TYPE
    { Type }
  | name = HOLE_NAME
    { Hole (name, None) }
  | DIM
    { Dim }
  | COF
    { Cof }
  | TOPC
    { TopC }
  | BOTC
    { BotC }
  | LBANG; t = ioption(term); RBANG
    { BoundaryHole t }

plain_atomic_term_except_name:
  | t = plain_atomic_term_except_sq
    { t }
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
  | spine = ioption(nonempty_list_left_recursive(name)); arg1 = atomic_term_except_name; args2 = list(atomic_term)
    { ap_or_atomic (List.concat [List.map term_of_name @@ Option.value ~default:[] spine; [arg1]; args2]) }
  | spine = nonempty_list_left_recursive(name)
    { ap_or_atomic (List.map term_of_name spine) }
  | t = term; DOT; lbl = user; spine = list_left_recursive(atomic_term)
    { ap_or_atomic ({ node = Proj(t, lbl); info = None } :: spine) }
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
  | SUC; t = atomic_term
    { Suc t }
  | LOOP; t = atomic_term
    { Loop t }
  | t = plain_lambda_except_cof_case
    { t }
  | ELIM; cases = cases
    { LamElim cases }
  | ELIM; scrut = atomic_term_except_sq; AS; mot = atomic_term; WITH; cases = cases
    { Elim { mot; cases; scrut } }
  | tele = nonempty_list(tele_cell); RIGHT_ARROW; cod = term
    { Pi (tele, cod) }
  | tele = nonempty_list(tele_cell); TIMES; cod = term
    { Sg (tele, cod) }
  | SIG; tele = list(field);
    { Signature tele }
  | STRUCT; tele = list(field);
    { Struct tele }
  | dom = term; RIGHT_ARROW; cod = term
    { Pi ([Cell {names = [`Anon]; tp = dom}], cod) }
  | dom = term; TIMES; cod = term
    { Sg ([Cell {names = [`Anon]; tp = dom}], cod) }
  /* So the issue is when we have a cofibration split case, we will have a bunch of pipe separated things
   We need to ensure that any patches occur in brackets...
   */
  | tp = term; AS; ps = patches
    { Patch (tp, ps) }
  | tp = term; HASH; ps = patches
    { Total (tp, ps) }
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
  | EQUATION; code = term; BEGIN; eqns = step; END
    { Equations { code; eqns } }

step:
  | tm = term; LSQEQUALS; pf = term; RSQ; r = eqns;
    { Equals (tm, pf, r) }
  | tm = term; LRSQEQUALS; r = eqns;
    { Trivial (tm, r) }

eqns:
  | s = step
    { Step s }
  | tm = term
    { Qed tm }

cases:
  | LSQ ioption(PIPE) cases = separated_list(PIPE, case) RSQ
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
    { ["zero"] }
  | SUC
    { ["suc"] }
  | BASE
    { ["base"] }
  | LOOP
    { ["loop"] }
  | lbl = path
    { lbl }


pat:
  | lbl = pat_lbl args = list(pat_arg)
   { Pat {lbl; args} }

pat_arg:
  | ident = plain_name
    { `Simple ident }
  | LBR i0 = plain_name RRIGHT_ARROW i1 = plain_name RBR
    { `Inductive (i0, i1) }

field:
  | LPR lbl = user; COLON tp = term; RPR
    { Field {lbl; tp} }

patch:
  | lbl = user; DOT_EQUALS; tp = term
    { Field {lbl; tp} }

patches:
  | LSQ ioption(PIPE) patches = separated_list(PIPE, patch) RSQ
  { patches }

tele_cell:
  | LPR names = nonempty_list(plain_name); COLON tp = term; RPR
    { Cell {names; tp} }
