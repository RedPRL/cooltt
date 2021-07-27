FROM alpine:3.14

# When a Docker action runs, it will bind the workspace to the following path.
VOLUME ["/github/workspace"]
WORKDIR /github/workspace

COPY cooltt.opam .
COPY entrypoint.sh /entrypoint.sh
RUN apk add --no-cache bash make m4 gcc git opam ocaml ocaml-compiler-libs rsync musl-dev \
    && opam init --disable-sandboxing --no-setup --compiler ocaml-system.4.12.0 --root /root/.opam \
    && opam pin add --root /root/.opam -y .

ENTRYPOINT "/entrypoint.sh"
