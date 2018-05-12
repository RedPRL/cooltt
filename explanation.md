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

## Data Types

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

One other design decision in the representation of terms under a
binders. In other words, what should `D.Lam` contain? Some
presentations of NbE make use of the host language's function space
for instance, so that `D.Lam` would take `D.t -> D.t`. For our
purposes though we opt for the "defunctionalized" variant where terms
under a binder are represented as closures. A closure is a syntactic
term paired with the environment in which it was being evaluated. This
means that a closure is a syntactic term with `n + 1` free variables
and an environment of length `n`. The idea is that the `i`th
environment entry corresponds to the `i + 1`th variable in the
term. This information is stored in the record `{term : Syn.t; env :
env}`. Since we have one term which binds 2 variables (the successor
case in natrec) there's also `clos2`. Its underlying data is the same
but we use it only for terms with 2 free variables.

One final remark about the data types, unlike before we use DeBruijn
levels (they count the opposite way) instead of indices. This choice
is advantage because it means we never need to apply a "shift". In
fact by doing binding in these two distinct ways we never need to
perform any sort of substitution or apply adjustment functions to any
of the terms throughout the algorithm.

## Evaluation

With the data types in place, next we turn to defining the two steps
describe above: evaluation and quotation. Evaluation depends on a
collection of functions:

``` ocaml
(* Utility function *)
val mk_var : D.t -> int -> D.ne

(* Compute various eliminators *)
val do_rec : D.clos -> D.t -> D.clos2 -> D.t -> D.t
val do_fst : D.t -> D.t
val do_snd : D.t -> D.t

(* Various "application" like moves *)
val do_clos : D.clos -> D.t -> D.t
val do_clos2 : D.clos2 -> D.t -> D.t -> D.t
val do_ap : D.t -> D.t -> D.t

(* Main evaluation function *)
val eval : Syn.t -> D.env -> D.t
```

The evaluation function depends on a good number of extraneous helper
functions. In order to explain it, let us first start with the helper
function and then consider each helper function as it arises.

``` ocaml
let rec eval t env =
  match t with
```

Evaluation starts by casing on the syntactic term `t` and includes on
case for every possible constructor. The case for variables is just
straightforward lookup. One benefit of using DeBruijn indices is that
it's quite straightforward to represent the environment as a list.

``` ocaml
  | Syn.Var i -> List.nth env i
```

The cases for `Nat` and `Zero` are also quite direct because there is
no computation to perform with either of them.

``` ocaml
  | Syn.Nat -> D.Nat
  | Syn.Zero -> D.Zero
```

The case for successor requires slightly more work. The subterm `t`
and `Syn.Suc t` needs to be evaluated. This is done just by recursing
with `eval`. There's no need to worry about adjusting the environment
since no binding takes place.

``` ocaml
  | Syn.Suc t -> D.Suc (eval t env)
```

Next comes the most complicated case, `Syn.NRec`. Recall that `NRec`
takes 4 arguments:

 - The motive, which binds 1 argument
 - The zero case, which binds 0 arguments
 - The successor case, which binds 2 arguments
 - The actual number, which binds 0 arguments

In order to evaluate `NRec` we have the following clause

``` ocaml
  | Syn.NRec (tp, zero, suc, n) ->
    do_rec
      (Clos {term = tp; env})
      (eval zero env)
      (Clos2 {term = suc; env})
      (eval n env)
```

Before we call the helper function `do_rec` to actually do the
recursion we evaluate the closed terms further and construct closures
for the terms we cannot evaluate further. Then `do_rec` will actually
perform the computation.

``` ocaml
let rec do_rec tp zero suc n =
  match n with
  | D.Zero -> zero
  | D.Suc n -> do_clos2 suc n (do_rec tp zero suc n)
  | D.Neutral {term = e} ->
    let final_tp = do_clos tp n in
    let zero' = D.Normal {tp = do_clos tp D.Zero; term = zero} in
    D.Neutral {tp = final_tp; term = D.NRec (tp, zero', suc, e)}
  | _ -> raise (Nbe_failed "Not a number")
```

This function works by casing on `n`. There are 3 cases to
consider. If `n` is `Zero` then we return the `zero` case. If `n` is
`Suc n'`, then we apply the closure `suc` to `n'` and `do_rec tp zero
suc n'`. Let us postpone explaining how `do_clos` and `do_clos2` works
for a moment and instead consider the last case. When `n` is neutral
we cannot evaluate `NRec` in an meaningful way so we construct a new
neutral term. This is done by using `D.Neutral`. This needs the
type of the result which is given by instantiating the motive's
closure with `n`: `do_clos tp n`. Next, we need to convert `zero` from
`D.t` into `D.nf` which again requires a type, constructed in an
analogous way: `do_clos tp D.Zero`. We then produce the final neutral
term:

``` ocaml
D.Neutral {tp = final_tp; term = D.NRec (tp, zero', suc, e)}
```

Now the instantiating of closures uses `eval` again. Remember that
closures are just environments and syntactic term but lacking the last
addition to the environment. This lacking value is what we need to
instantiate the binder. Once we have that, we can just use `eval` to
normalize the term.

``` ocaml
let do_clos (Clos {term; env}) a = eval term (a :: env)

let do_clos2 (Clos2 {term; env}) a1 a2 = eval term (a2 :: a1 :: env)
```

Returning to `eval`, the next set of cases deal with `Pi`. Evaluating
`Syn.Pi` proceeds by normalizing the first subterm and creating a
closure for the second.

``` ocaml
  | Syn.Pi (src, dest) ->
    D.Pi (eval src env, (Clos {term = dest; env}))
```

Similarly for lambdas we just create a closure.

``` ocaml
  | Syn.Lam t -> D.Lam (Clos {term = t; env})
```

The case for application is slightly more involved. We do something to
similar to `do_rec`, it appeals to the helper function `do_ap`.

``` ocaml
  | Syn.Ap (t1, t2) -> do_ap (eval t1 env) (eval t2 env)
```

This helper function `do_ap` is similar to `do_rec`. It takes the
normalized subterms and performs the application when possible,
constructing the neutral term when it's not.

``` ocaml
let do_ap f a =
  match f with
  | D.Lam clos -> do_clos clos a
  | D.Neutral {tp; term = e} ->
    begin
      match tp with
      | D.Pi (src, dst) ->
        let dst = do_clos dst a in
        D.Neutral {tp = dst; term = D.Ap (e, D.Normal {tp = src; term = a})}
      | _ -> raise (Nbe_failed "Not a Pi in do_ap")
    end
  | _ -> raise (Nbe_failed "Not a function in do_ap")
```

This helper function again makes use of `do_clos` to actually do the
application. One quick point is that when applying a neutral type we
actually needed the type it was annotated with. Without this we could
not have determined the type to use for `D.Normal`.

The case for universes is quite direct, we just convert `Syn.Uni i`
to the corresponding `D.Uni i`.

``` ocaml
  | Syn.Uni i -> D.Uni i
```

All that's left is the cases for sigma types. The case for `Syn.Sig`
is identical to the case for `Syn.Pi`.

``` ocaml
  | Syn.Sig (t1, t2) -> D.Sig (eval t1 env, (Clos {term = t2; env}))
```

The case for pairs proceeds by evaluating both the left and the right
half and packs them back into `Syn.Pair`.

``` ocaml
  | Syn.Pair (t1, t2) -> D.Pair (eval t1 env, eval t2 env)
```

All that remains are the eliminators: `Fst` and `Snd`. For these we
again just appeal to some helper functions

``` ocaml
  | Syn.Fst t -> do_fst (eval t env)
  | Syn.Snd t -> do_snd (eval t env)
```

These helper functions again perform the evaluation if it's possible
and if it's not they construct a new neutral term. The only slight
complication is that `do_snd` must appeal to `do_fst`. This
dependency comes from the fact that the type of `Snd` mentions `Fst`:
`fst p : B (snd p)` if `p : Sig A B`. Below is the code for `do_snd`
since it includes everything interesting about `do_fst` so I have
elided it.

``` ocaml
let do_snd p =
  match p with
  | D.Pair (_, p2) -> p2
  | D.Neutral {tp = D.Sig (_, clo); term = ne} ->
    let fst = do_fst p in
    D.Neutral {tp = do_clos clo fst; term = D.Snd ne}
  | _ -> raise (Nbe_failed "Couldn't snd argument in do_snd")
```

## Read Back/Quotation
