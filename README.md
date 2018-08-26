## blott

An implementation of Normalization by Evaluation for Martin-Löf Type Theory with
dependent products, dependent sums, natural numbers, box, later, and a
cumulative hierarchy. This implementation correctly handles eta for later, box,
pi, and sigma.

Once built, the executable `blott` may be used to type check and normalize
programs. A program consists of a series of definitions: `let x : tp = term` and
commands to normalize programs: `normalize def name` or `normalize term at
tp`. For examples, see the `test/` directory.
