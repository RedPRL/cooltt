FROM alpine:3.14 AS build

WORKDIR "/src/"

# ocaml, ocaml-compiler-libs | OCaml
# opam                       | OPAM
# make, m4, musl-dev         | Requird by many OPAM packages
# git                        | Get yuujinchou and bantorra
RUN \
  apk add --no-cache opam ocaml ocaml-compiler-libs make m4 musl-dev git && \
  opam init --disable-sandboxing --disable-completion --no-setup --yes

# If only the OPAM is modified, Docker should start from here.
# We copy dune-project because dune _could_ generate OPAM files from dune-project (not used in cooltt)
COPY ["dune-project", "cooltt.opam", "./"]
RUN opam install --deps-only --with-test --yes "./"

# If only the source is modified, Docker should start from here.
COPY ["src", "./"]
# We use dune instead of opam because of the --profile option
RUN \
  opam exec -- dune build --profile static && \
  opam exec -- dune install --section bin && \
  cp "`opam config var bin`/cooltt" /cooltt

# If only test cases are modified, Docker should start from here.
COPY ["test", "./"]
RUN opam exec -- dune runtest

# Harness the power of static linking
FROM scratch
COPY --from=build ["/cooltt", "/"]

ENTRYPOINT ["/cooltt"]
