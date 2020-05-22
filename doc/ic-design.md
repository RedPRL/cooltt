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

*this isn't exhaustive and also won't be a top level heading in the final
version*

1. what are the names of the imported identifiers? (Are they qualified?)
1. Do we need to keep track of whether an identifier comes from this file
   or an imported file?
1. Re: the diamond problem, do we need to make sure that all references to
   an imported identifier are judgmentally equal?
1. What happens if identifiers are shadowed?

1. what is the output of checking that is cached? how do you compare those
   things for equality?
1. what needs to be done while reading the cache to restore that state?
1. how do you patch a bunch of these together? Suppose a file includes
   multiple other files that have both been cached already; we need to
   create a "combined" state that has both of them loaded somehow

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

## Judgemental Changes

 - judegmental flattening, `flat u u'`; u is a cooltt unit that
   includes `import` declarations and `u'` is a cooltt unit that does
   not

 - elaborating a file now has to change to deal with this new decl

 - checking a unit u with no caching at all

 - checking a unit u with respect to some cache (should be sort of arbitrary)

## selected rules

## Theorems

1. [consistency]

   ```
     For all decls : ?? , s : ??, u1 u2 : ??, cache : ??,

     If (decls ok), and
		(flat s s'), and
	    (decls ⊢ s' ~> u1), and
		(decls | cache ⊢ s ~> u2), then
     u1 = u2
   ```

	"If the source of a unit `u` is checked with no cache and produces
	output `u1`, and it is checked with caching and produces output `u2`,
	then `u1 = u2`."
