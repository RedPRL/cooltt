## nbe-for-mltt explained

The goal of this document is to give an explanation of
`src/lib/nbe.ml`. The rest of the code in this repository is just
scaffolding to allow the user to quickly interact with this code and
not of much interest.

First, let us define the type theory we're working with. It's a fairly
standard Martin-Löf type theory. I will not write down all the typing
rules since most are obvious and instead list the syntax of the type
theory.

 - We have natural numbers, so a type `Nat` with constructors `zero`
   and `(suc t)`. There is an elimination form
   `(nrec (n motive) z (p i s) n)`. This elimination form is
   characterized by the following rules

        (nrec (n motive) z (p i s) zero) ↦ z : (ap motive zero)
        (nrec (n motive) z (p i s) (suc n)) ↦ (ap (ap s n) (nrec ... n)) : (ap motive (suc n))

   For the convenience of the user of the system, plain old numeric
   literals are supported.

 - Dependent functions are standard, there is `(Pi from (x to))` and
   `(lam (x body))`. This type theory includes an eta rule for lambdas
   so that

        f = (lam (x (ap f x)))

 - Dependent pairs are also standard with `(Sig fst (x snd))` and
   `(pair l r)`. It comes equipped with the negative formulation of
   the eliminator: `(fst p)` and `(snd p)`. Like for functions,
   there's a corresponding eta rule

        p = (pair (fst p) (snd p))

 - Finally, there are universes. They don't do much of anything
   special in this code but there's a cumulative hierarchy.

The goal of this code is quite simple: take a term and its type in
this language and produce its beta-normal eta-long form. This
procedure is more than merely evaluating it: normalization like this
will proceed under binders and ensure that everything is fully
eta-expanded. This is useful because it produces a canonical member of
the equivalence class a term belongs to. Checking equivalence between
two terms can be done by normalizing and then comparing for alpha
equivalence. In particular, this is useful in something like a
type-checker where we might want to compare types for beta-eta
equality.

The central idea of this code, and normalization by evaluation in
general, is to break up the process of producing a normal form into
distinct steps. We first "evaluate" the code into a new representation
which does not admit any beta reductions and simultaneously tag every
part of the term that might need eta expansion. This representation is
the "semantic domain". Next we "quote" the term from the semantic
domain back into the syntax and perform the tagged eta
expansions. There are many variants on NbE but this variant seems
to strike a pleasant balance between scalability and simplicity.

First let us review the representation of the surface syntax.

``` ocaml
type uni_level = int
type t =
  | Var of int (* DeBruijn indices for variables *)

  (* nats *)
  | Nat
  | Zero
  | Suc of t
  | NRec of (* BINDS *) t * t * (* BINDS 2 *) t * t

  (* functions *)
  | Pi of t * (* BINDS *) t
  | Lam of (* BINDS *) t
  | Ap of t * t

  (* pairs *)
  | Sig of t * (* BINDS *) t
  | Pair of t * t
  | Fst of t
  | Snd of t

  (* universes *)
  | Uni of uni_level

type env = t list
```

This representation of terms is fairly standard. It is worth taking a
moment to clarify the binding structure. We use De Bruijn indices for
representing variables so the binding in terms is silent. In the
above, I have annotated which subterms bind variables with `(* BINDS
*)` and `(* BINDS 2 *)` in the case of the "successor" case of natrec
which binds 2 variables.

As is good style, all of these declarations are contained in the
module `Syn`.

Next up is the semantic domain. The semantic domain is stratified into
3 separate syntactic categories: values, normal forms, and neutral
terms. These are represented with 3 different OCaml types and are all
contained in the module `D`.

``` ocaml
type env = t list
and clos = Clos of {term : Syn.t; env : env}
and clos2 = Clos2 of {term : Syn.t; env : env}
and t =
  | Lam of clos
  | Neutral of {tp : t; term : ne}
  | Nat
  | Zero
  | Suc of t
  | Pi of t * clos
  | Sig of t * clos
  | Pair of t * t
  | Uni of Syn.uni_level
and ne =
  | Var of int (* DeBruijn levels for variables *)
  | Ap of ne * nf
  | Fst of ne
  | Snd of ne
  | NRec of clos * nf * clos2 * ne
and nf =
  | Normal of {tp : t; term : t}
```

All 3 of the categories are mutually recursive. Values, in the code
`t`, contain terms which have evaluated to a constructor which does
not need to be reduced further. So for instance, `Lam` and `Pair` may
contain computation further inside the term but at least the outermost
constructor is stable and fully evaluated. Now goal is normalization,
which means that we have to deal with open terms. Even if at the
top-level we were to only invoke this procedure on closed terms in
order to normalize under a `Lam`, `Pi`, `Sig`, etc it becomes
necessary to work with open terms.

This means that we have to consider the case that something wants to
reduce further before becoming a value but cannot because its blocked
on something. These are called neutral terms. The canonical example of
a neutral term is just a variable `x`. It's not yet a value but
there's no way to convert it to a value since we have no information
on what `x` is yet. Similarly, if we have some neutral term and we
apply `Fst` to it it's clearly still not a value. On the other hand,
we don't have any way of reducing it further so what's there to
do. There's a way of including neutral terms into the general category
of values with the constructor `Neutral`. This constructor comes
equipped with a type annotation which will prove important later for
bookkeeping purposes.

All in all, this means we have a syntactic category comprised of
"eliminators stacked onto variables" and that is all that `ne` is. The
final category, `nf`, is a special class of values. It comes from the
particular style of NbE that we're doing, it associates a type with a
value so that later during quotation we can eta expand it
appropriately. In literature this is usually written as a shift,
↑ᴬ. Since we use `nf` in various places this ensures that as we go
through the process of quotation we always have sufficient annotations
to determine how to quote a term.

TODO closures

One final remark about the data types, unlike before we use DeBruijn
levels (they count the opposite way) instead of indices. This choice
is advantage because it means we never need to apply a "shift". In
fact by doing binding in these two distinct ways we never need to
perform any sort of substitution or apply adjustment functions to any
of the terms throughout the algorithm.

With the data types in place, next we turn to defining the two steps
describe above: evaluation and quotation. Evaluation depends on a
collection of functions:
``` ocaml
mk_var : D.t -> int -> D.ne
do_rec : D.env -> D.clos1 -> D.t -> D.clos2 ->
```
