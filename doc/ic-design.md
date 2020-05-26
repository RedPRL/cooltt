_This document is currently a *rough draft*. Do not take anything written
here as gospel; it's partial and what is here is all up for negotiation, in
progress, and likely just plain incorrect in many instances. This
disclaimer will be removed in the future once we've discussed the draft and
it gets promoted to working spec._

# Incremental Checking in cooltt

This document describes a system for incremental checking (IC) of cooltt
files in the style of incremental compilation with TILT (see
[http://www.cs.cmu.edu/~rwh/papers/smlsc/mlw.pdf]). The goal is to allow
cooltt developments to be broken up into separate _units_. Once a unit is
checked, the result will be cached until its source changes, so that
subsequent units that depend on it may be checked without redundant work.

At present this design does not include a notion of "separate checking", by
analogy to separate compilation, at the very least because cooltt does not
have interfaces. Extending cooltt with interfaces and the other features of
a more robust module system is an fun possible future project but currently
out of scope.

## High Level Summary

### RedTT Solution
Terms of the core language are serialized to disk by producing a JSON
representation of the term and then gzipping it. This is stored in a `rot`
file, so for example the result of loading a file `f.red` would be stored
in `f.rot`. When RedTT starts, it produces a cache of these terms from the
`rot` files present. To load the contents of a file, proceed as follows:

1. Check the cache to see if you need to typecheck it at all.
1. If it's present in the cache, is it up to date?
    1. If it is, use the cached version instead of checking the file.
    1. If it is not, check the file (and recursively check its
       dependencies), and update the cache. Then, compute which other
       modules depend on the file in question and recheck them against the
       new version of the current file.

### Goals
1. Within reason, implement an IC mechanism that is modular and not
   intertwined with the particular cooltt code base (and therefore could be
   reused for other systems later).

1. Do not needlessly depend on ocaml internals -- i.e. don't use the built
   in `Marshal` functionality -- in favor of rolling our own free-standing
   solutions.

1. Do not make egregiously large cache files. (RedTT solved this by using
   `gzip`, which is very good at compressing highly repetitive core terms
   expressed as JSON.)

1. Make a reasonably performant IC mechanism, but favor ease of inspection,
   extension, and verification of the implementation over raw performance.

1. Do not conflate IC with designing a module system for cooltt. Rather,
   make an IC mechanism that will allow for experimentation with different
   ideas for module systems later.

1. Do not conflate IC with designing a powerful import syntax (à la
   https://github.com/RedPRL/redtt/issues/449), but again make an IC
   mechanism that will admit future experimentation.

## questions this design needs to answer

_this list isn't exhaustive nor are the answers conclusive! this section
won't even exist in the final version, it's more of a todo list to make
sure i don't forget to address things that have been brought up; tentative
answers below each_

1. what are the names of the imported identifiers? (Are they qualified?)
   - i think they should be fully qualified all the time for now; i don't
     want to worry about "open" style directives right now because it's a
     whole other kettle of fish.

1. Do we need to keep track of whether an identifier comes from this file
   or an imported file?
   - i suspect probably not, just looking at the implementation in
     `Driver.ml`. right now, when decls get elaborated they are added as
     globals along with their type; i don't see why you wouldn't want to do
     that recursively into includes as well.

1. Re: the diamond problem, do we need to make sure that all references to
   an imported identifier are judgmentally equal?
   - i don't understand this question yet. my intuition is that there
     shouldn't be copies of the elaborated version of anything, and that
     all references should be to that one entity. but i don't think that's
     really an answer to this question and i'll have to come back to it and
     figure out what i'm missing. (TODO)

1. What happens if identifiers are shadowed (or clash)?
   - my temptation right now is to only define elaboration when identifiers
     are unique, that is to say if you have two units named `Nat`, that's
     an elaboration error. i'll try to reflect this in the judgemental
     structure below;i think this is in line with the `decls ok` judgement
     from the TILT paper that rules out irritating ambiguities about names
     of things.

1. what is the output of checking that is cached? how do you compare those
   things for equality?
   - as a first cut i think you can read this off from the elaborator,

     ```
     elaborate_typed_term : string ->   //the identifier
         ConcreteSyntaxData.cell list -> // args from the parse tree
         ConcreteSyntax.con ->    // type from the parse tree
         ConcreteSyntax.con ->    // body, or definition from the parse tree
         (SyntaxData.tp * DomainData.tp * SyntaxData.t * DomainData.con) m
     ```
     so elaboration at least of a definition produces a syntactic term and
     type and a semantic term and type


1. what needs to be done while reading the cache to restore that state?
   - TODO

1. how do you patch a bunch of these together? Suppose a file includes
   multiple other files that have both been cached already; we need to
   create a "combined" state that has both of them loaded somehow
   - TODO

## Syntactic Changes

### Unit Paths
"Unit paths" are names used in import statements for units:

```
p ::= s | s.p
```
Here, `s` is a string from some reasonable collection of strings--at a
minimum I think we can support `[A-Za-z0-9]`, but it certainly cannot
contain `..`, `.`, `\`, `/`, etc.

cooltt will be responsible for mapping unit paths to operating system
specific filesystem paths in some way. There is some flexibility in this; a
few choices include:

1. a totally flat name space, where all unit paths are resolved to files in
   the same directory, so `a.b.c` resolves to `c.cooltt`. This is
   simplistic and just enough to get off the ground but leave room to
   change.
1. unit paths are resolved by mapping into a subset of file system paths
   rooted at the top level of the library, so `a.b.c` resolves to
   `a/b/c.cooltt`.
1. define an auxiliary mapping file that gives the resolution of unit names
   to file system paths explicitly and is maintained by the programmer.
1. some hybrid of options (2) and (3), where there is a default resolution
   of unit paths to file system paths, but if a mapping file is present
   then it overides that default. this is an attempt to balance the
   concerns of avoiding the complixities of the file system, but also not
   burdening the programmer with the generation of too much boilerplate.

### Extension to the syntax of cooltt

The concrete syntax of cooltt declarations is extended with a form for
_imports_

```
decl ::= def ... | print ... | normalizeterm ... | quit | import p
```

## Semantics

### TILT style judgemental structure

bad naming problem: above, `decl` is the syntactic class of declarations in
the cooltt grammar, as in `Grammar.mly`. In the TILT paper, `decs` is a
semantic object that acts like a context for elaboration

"a declaration list decs declares expression (var:con), constructor
(var:knd), and module (var:sig) variables. a structure declaration list has
the form

 lab1 > dec1, ... , labn > decn

giving a label to each declaration. The structure declaration list
lab>dec,sdecs binds the variable declared by dec with the scope sdecs."


### changes and additions
 - in the theorems below, we wish to be able to state the property that
   that the new elaboration judgement that refers to a cache does the same
   thing as the existing non-caching elaboration. to do that, we need to be
   able to relate the source of a unit that includes `import` statements to
   the source of an equivalent unit that does not -- this amounts of a
   judgemental of elaborating `import` statements.

   we call this judgemement `flat : src → src0 → U`, where `src0` is the
   language of cooltt that does not include `import`.

 - we write the existing, non-caching, elaboration judgement `?? ⊢ s ~> u`,
   where `s` is a term in the external language of cooltt and `u` is the
   unit of the internal language that is the output. ?? is the context
   under which the elaboration occurs. TODO what is ??.

 - we write the caching-elaboration judgement `?? | c ⊢ s ~> u , c'` where
   `s,u,??` are as before, but `c` is the cache in which the elaboration
   takes place and `c'` is the cache at the end of elaboration. by making
   the cache after elaboration an explicit output, we can state theorems
   like Stability, below. TODO check the name here.

 - TODO: what exactly are the types of ctx and cache? both are mappings.

 - TODO: define: Γ ok — it's whatever the right thing is to make it a
   mapping, so no duplicated names at least, probably other similar things.

definition used below; updating a context with respect to just one element
of its domain and leaving everything else alone.
```
update : name → ?? → cache → cache → U
update r d c c' = (r ∈ dom c) and (c without r = c' without r) and (c' maps r to d)
```

TODO: delete crap that doesn't make sense.

TODO: to define Γ | c ⊢ s ~> u , c' -- case on s! start with empty; if s is an
import, check the file age and if tehre's a cache, load that if you can;
otherwise recurr

### new rules corresponding to additions

## Theorems

thoughts from carlo: anything that feels like "the changes you make don't
disrupt anything" is barking up the wrong tree. sometimes code changes and
it's wrong. so don't think about consistency of a change with respect to a
cache or whatever.

instead, you want to know that the addition of the cache itself isn't
changing the result EVEN IF THAT RESULT IS A FAILURE. "loading the cache is
the same as loading the file".

where does the cache come from? you still start from empty when you're
reading a file and then as you go down the list of decls, go by cases; when
you get to the import case, call out to an abstract LOAD action or
something.



1. [consistency]

	"Flattening a term and elaborating it as usual produces the same output
    and cache as elaborating it starting from the empty cache".

   ```
     For all Γ : ctx , s s' : external-term, u1 u2 : internal-term, c' :
	 cache,

     If (Γ ok), and
        (?? ⊢ flat s s'), and   [ not the same ctx? ]
        (Γ ⊢ s' ~> u1), and
        (Γ | ∅ ⊢ s ~> u2 , c'), then
     u1 = u2
   ```

	NB: i could state this in a little bit stronger of a way but i don't
    think there's much point. really you can have any cache with dom(c) ∩
    names(s') = ∅ – you can have whatever garbage you want in there as long
    as you never use it. but that just makes it sort of "morally empty";
    you could show that you can swap such a context for empty and it'd be
    equivalent.

	if that intersection isn't empty and the types happen to agree — geez,
    i have no idea. that could be ok? if the types don't agree then it'll
    break for sure. you can't compile code against a library with the same
    names and different types and expect that to make sense.

	i think that this version is fine; the version with an empty
    intersection is morally the same; the version with a consistent but
    non-empty cache is a different theorem, like resumability or something.


2. [ idempotence? ]

    "If the source of a unit is checked with a cache, and then something in
    that cache changes in a way that doesn't change its signature, and the
    source of that unit is checked again against the new cache, the results
    are the same"

   ```
     For all Γ : ctx , s : external-term , u1 u2 : internal-term, c1 c2 c1'
     c2' : cache, d1 d2 : ??,

     If (Γ ok), and
        (r,d1) ∈ c1, and
        (r,d2) ∈ c2, and
		c1 / r = c2 / r, and     [ this is kind of a stupid way to say this.]
		[something about d1 being morally the same as d2], and
        Γ | c1 ⊢ s ~> u1 , c1', and
        Γ | c2 ⊢ s ~> u2 , c2', then
     u1 = u2 and c1' = c2' [probably?]
   ```

3. [ stability? ]

   "if you elaborate a term starting with the empty cache, then change
   something in the resultant cache in a compatible way, then recheck the
   unit with that new cache, you get the same output."

   e.g. if data.nat defines addition, and you check something against it,
   then change data.nat to define addition by recursion on the other
   argument, you should still get the same cache and the same result.

   but that may not be true? maybe it's like a transport over that change or
   something complicated; it's only judgementally the same not
   definitionally the same? in the case of changing addition, you get
   different definitional equalities as a result of which argument you
   recurr on, so dependent code may not type check even though + : Nat ->
   Nat -> Nat in both cases

   ```
     For all Γ : ctx, s : external-term, u1 u2 : internal-term, c c' c'' :
     cache, d : ??,

     If (Γ ok), and
        (Γ | ∅  ⊢ s ~> u1 , c), and
		update r d c c'
        (Γ | c' ⊢ s ~> u2 , c''), then
     u1 = u2 and c' = c''
   ```
