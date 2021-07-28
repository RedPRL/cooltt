### STAGE opam START
### Prepare the Docker with basic dependencies

FROM alpine:3.14 AS opam

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
RUN ["opam", "install", "--deps-only", "--yes", "./"]

# If only the source is modified, Docker should start from here.
COPY ["src", "Makefile", "./"]

### STAGE opam END

############################################################################

### STAGE build START
### Build statically-linked cooltt

FROM opam AS build

# We use dune instead of opam because of the --profile option
RUN \
  opam exec -- dune build --profile static && \
  opam exec -- dune install --section bin && \
  cp "`opam config var bin`/cooltt" /cooltt

### STAGE build END

############################################################################

### STAGE test START
### Test cooltt

FROM build AS test

RUN opam install --deps-only --with-test --yes "./"

# If only test cases are modified, Docker should start from here.
COPY ["test", "./"]

RUN ["make", "test"]

ENTRYPOINT []

### STAGE test END

############################################################################

### STAGE doc START
### Generate cooltt documentation

FROM opam AS doc

RUN opam install --deps-only --with-doc --yes "./"

RUN ["make", "doc"]

ENTRYPOINT ["cp", "-a", "_build/default/_doc/_html"]
CMD ["/output/"]

### STAGE doc END

############################################################################

### STAGE deploy START
### Place statically-linked cooltt in an empty image

FROM scratch AS deploy

COPY --from=build ["/cooltt", "/"]

ENTRYPOINT ["/cooltt"]

### STAGE test END
