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
answers below each

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
_imports_ (the rest is unchanged)

```
decl ::= def ... | print ... | normalizeterm ... | quit | import p
```

## Semantics

### Summary

A cooltt file, once lexed and parsed, is a list of declarations following
the grammar above. Those declarations are processed in order of appearance,
first by the elaborator which renders them into tactics and then by running
those tactics to produce terms in the internal language. Running these
tactics includes expensive calls to procsses like
normalization-by-evaluation. This is the expensive work that we wish to
avoid doing more than once.

To that end, we will equip elaboration with a _cache_ that maps names (as
in the `def` declaration form) to the internal language terms resulting
from the above process. When elaborating a definition, the cache will be
consulted and updated as needed before proceeding.

As a related but also somewhat separate concern, we also extend the
language to include `import` statements. This allows cooltt developments to
be broken up into multiple files. When a file has been checked, the cache
of its names and their paired terms will be written out to disk. When other
files `import` another unit, the cache can be loaded back into memory from
disk, merged with any possible current cache, and then we proceed as before
but with the benefit of stored work done previously.

In a given run of the elaborator, the cache starts out empty and is
populated as needed and as possible given the imports present in a
particular development, the files present on disk, and their relative age
with respect to the source files they represent.

Note that no attempt will be made to verify that the cache files written to disk
are indeed the output of previous runs of cooltt; they will be read in good
faith, if they are in the right format, and used. It is therefore possible
that a user could _spoof_ a cache file by learning the format and writing
one by hand. We do not attempt to protect ourselves from that attack;
cooltt developments can be checked from scratch, with no cache files on
disk, to provide ground-up evidence that they check as written.

A judgemental description of this process is below, followed by statements
of a few theorems that attempt to characterize some aspects of it.

### Judgemental Summary

A cooltt file is a list of declaractions, each one given by

```
decl ::=  def {name : Ident.t, ...}
        | print ...
	    | normalizeterm ...
		| quit
		| import p
```

A cache maps `Ident.t` to terms in the internal language.

Elaboration of each declaration in sequence produces one of two outcomes,
either a positive or negative depending on whether the declaration is
well-formed.

```
result ::= Continue | Quit
```

The material results of elaboration are stored in an environment, `Γ`,
mapping names to internal terms in the same way as the cache. The
difference between the two is that the environment is built up
incrementally through one run of the system, rather than referring to
anything on disk from previous runs.

We describe elaboration with the judgement `Γ | c ⊢ ds ~> r , c'` where `Γ`
is an environment, `c c'` are caches, `ds` is a list of declarations, and
`r` is a result. We pun this judgement with an identical form that
considers single declarations, while the form that considers a list of
declarations reflects the monoidal struture of lists by iterating through
and collecting the results as needed.

_TODO: define `Γ ok` following TILT paper, at least that there aren't
duplicate names so that it works as a mapping. probably need `c ok` too for
caches that has almost the same rules_


Rules for processing a list of declarations:
```
—————————————————————–[eof]
Γ | c ⊢ [] ~> Quit , c


Γ | c ⊢ d ~> Quit , c'
———————————————————————————–[quit]
Γ | c ⊢ d :: ds ~> Quit , c'


Γ | c ⊢ d ~> Continue , c'
———————————————————————————–[cont]
Γ | c ⊢ d :: ds ~>  , c'
```

Rules for each declaration:

The rules for `import` and `def` are the most interesting here. We omit the
rules for `normalizeterm` and `print` entirely, since they're not in scope
and invoke other IO effects (e.g. printing things to the screen for the
user to inspect).
```
—————————————————————–—–[quit]
Γ | c ⊢ quit ~> Quit , c


```

TODO: to define Γ | c ⊢ s ~> u , c' -- case on s! start with empty; if s is an
import, check the file age and if there's a cache, load that if you can;
otherwise recurr


## Theorems

In general, it is not the responsibility of the caching mechanism (or the
elaborator more generally) to make any promises about the quality of the
code in the libraries; any reasoning that feels like "changes made to the
files on disk do not disrupt anything" is not correct.

For example, imagine a library of natural numbers that offers a definition
of addition and some client code that imports it. If that definition of
addition changes from recurring on the first to the second argument, the
client gets different definitional and judgemental equalities about the
defined operation: the code is different even though it has the same name
and type. Such a breaking change must cause changes in the clients that use
it; it is not up to the caching mechanism to defend against or detect or
fix situations like this.

Instead, we want to capture the idea that loading a result stored in the
cache produces the same effect as re-checking the file that produced
it--even if that result is in the negative.

To this end, we offer two theorems that should hold. The first,
consistency, reflects the intuition that XXX. The second, XXX, reflects the
intuition that XXXX.

1. [consistency]

	"Flattening a term and elaborating it as usual produces the same output
    and cache as elaborating it starting from the empty cache".

	we wish to be able to state the property that that the new elaboration
	judgement that refers to a cache does the same thing as the existing
	non-caching elaboration. to do that, we need to be able to relate the
	source of a unit that includes `import` statements to the source of an
	equivalent unit that does not -- this amounts of a judgemental of
	elaborating `import` statements.

	we call this judgemement `flat : src → src0 → U`, where `src0` is the
	language of cooltt that does not include `import`.

	we write the existing, non-caching, elaboration judgement `?? ⊢ s ~>
	u`, where `s` is a term in the external language of cooltt and `u` is
	the unit of the internal language that is the output. ?? is the context
	under which the elaboration occurs. TODO what is ??.

   ```
     For all Γ : ctx , s s' : external-term, u1 u2 : internal-term, c' :
	 cache,

     If (Γ ok), and
        (?? ⊢ flat s s'), and   [ not the same ctx? ]
        (Γ ⊢ s' ~> u1), and
        (Γ | ∅ ⊢ s ~> u2 , c'), then
     u1 = u2
   ```

	_Aside: i could state a superficially stronger vesion of this but i
    don't think there's much point. really you can have any cache with
    `dom(c) ∩ used_names(s') = ∅`, that is you can have whatever garbage
    you want in there as long as you never use it. but that just makes it
    sort of "morally empty"; you could show that you can swap such a
    context for empty and it'd be equivalent. it doesn't describe a richer
    relationship between the two judgements especially.

	if that intersection isn't empty and the types happen to agree – that
    could be OK but this is veering off sharply into the wrong way of
    thinking about this problem. it's not up to the cache mechanism to care
    if the code checks or not, only to do a full and faithful rendition of
    the non-cached mechanism._

2. [ xx ]
