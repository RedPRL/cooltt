# Image Tags

- `edge`: This is the “best” version of cooltt, built as a standalone binary file with zero dependencies.

- `builder-<branchname>`: These images are the ones with static `cooltt` built for each branch using the `base`
  image. GitHub caching is enabled to preserve intermediate layers of this stage. They contain a working version
  of `cooltt`, but are much larger than `edge` because they contain the full building environment. Testing and
  documentation generation are done using these images.

- `base`: This is the our customized Alpine Linux with OCaml, OPAM, and many OPAM packages installed.
  They only depend on `cooltt.opam`. It is expected that the same image can be used for all branches for months.
  The `base` image is purely for efficiency. Correctness is still guaranteed even if the OPAM files have been changed.
