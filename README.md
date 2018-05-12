## nbe-for-mltt

An implementation of Normalization by Evaluation for Martin-Löf Type
Theory with dependent products (pi), dependent sums (sigma), natural
numbers, and a cumulative hierarchy. This implementation correctly
handles eta for both pi and sigma.

It is heavily based on the description provided in "Normalization by
Evaluation Dependent Types and Impredicativity" by Andreas Abel.

Once built, the executable `nbe` may be used to normalize programs.
Simply feed it a file containing two sexprs, a term and a type. An
explanation of the algorithm may be found in `explanation.md`.
