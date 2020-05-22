# design for incemental checking in cooltt


## High Level Summary of RedTT's Solution
Terms of the core language are serialized to disk by producing a JSON representation of the term and then gzipping it. This is stored in a `rot` file, so for example the result of loading a file `f.red` would be stored in `f.rot`. When RedTT starts, it produces a cache of these terms from the `rot` files present. To load the contents of a file, proceed as follows:

1. Check the cache to see if you need to typecheck it at all.
1. If it's present in the cache, is it up to date?
    1. If it is, use the cached version instead of checking the file.
    1. If it is not, check the file (and recursively check its dependencies), and update the cache. Then, compute which other modules depend on the file in question and recheck them against the new version of the current file.

## Goals for cooltt
* Within reason, implement a version of this process that is not very intertwined with the particular cooltt code base (and therefore could be reused for other systems later).
* Do not depend on any ocaml internals -- i.e. don't use the built in `Marshal` functionality -- in favor of rolling our own free-standing solutions because the domain of the problem is comparatively quite simple.
* Do not make egregiously large cache files (RedTT solved this by using gzip, which is very good at compressing highly repetitive core terms expressed as JSON.)
* Have the cache operations be reasonably performant, but perhaps a little slower in favor of being easy to inspect and verify.

## Things To Avoid
1. I don't want to get into the business of designing the perfect module system for cooltt. That is a worthwhile and very interesting endeavor but not the point of this issue (and the PR that will eventually close it). Rather, I want to make something that will work now and be extensible to whatever module system we might end up deciding on.

2. Similarly, I want what I implement to not get in the way of future namespace management designs (à la https://github.com/RedPRL/redtt/issues/449), but I don't want to get entangled with figuring out exactly what those should be. That is an important but separate concern.

## questions (this won't be the top level heading)

1. what are the names of the imported identifiers? (Are they qualified?) 
2. Do we need to keep track of whether an identifier comes from this file or an imported file? 
3. Re: the diamond problem, do we need to make sure that all references to an imported identifier are judgmentally equal? 
4. What happens if identifiers are shadowed?

1. what is the output of checking that is cached? how do you compare those things for equality?
2. what needs to be done while reading the cache to restore that state?
3. how do you patch a bunch of these together? Suppose a file includes multiple other files that have both been cached already; we need to create a "combined" state that has both of them loaded somehow

## syntactic forms

### Unit Paths
"Unit paths" are names used in import statements for units:

```
p ::= s | s.p
```
Here, `s` is a string from some reasonable collection of strings--at a minimum I think we can support `[A-Za-z0-9]`, but it certainly cannot contain `..`, `.`, `\`, `/`, etc.

cooltt will be responsible for mapping unit paths to operating system specific filesystem paths in some way. There is some flexibility in this; a few choices include:

1. a totally flat name space, where all unit paths are resolved to files in the same directory, so `a.b.c` resolves to `c.cooltt`. This is simplistic and just enough to get off the ground but leave room to change.
1. unit paths are resolved by mapping into a subset of file system paths rooted at the top level of the library, so `a.b.c` resolves to `a/b/c.cooltt`.
1. define an auxiliary mapping file that gives the resolution of unit names to file system paths explicitly and is maintained by the programmer.
1. some hybrid of options (2) and (3), where there is a default resolution of unit paths to file system paths, but if a mapping file is present then it overides that default. this is an attempt to balance the concerns of avoiding the complixities of the file system, but also not burdening the programmer with the generation of too much boilerplate.
