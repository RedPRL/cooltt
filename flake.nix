{
  description = "Experimental implementation of Cartesian cubical type theory";

  inputs = {
    opam-nix.url = "github:tweag/opam-nix";
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.follows = "opam-nix/nixpkgs";
  };

  outputs = { self, flake-utils, opam-nix, nixpkgs }@inputs:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        on = opam-nix.lib.${system};
        localPackagesQuery = builtins.mapAttrs (_: pkgs.lib.last)
          (on.listRepo (on.makeOpamRepo ./.));
        devPackagesQuery = {
          ocaml-lsp-server = "*";
          ocp-indent = "*";
          merlin = "*";
        };
        query = devPackagesQuery // {
          ocaml-base-compiler = "*";
        };
        scope = on.buildDuneProject { } "cooltt" ./. query;
        devPackages = builtins.attrValues
          (pkgs.lib.getAttrs (builtins.attrNames devPackagesQuery) scope);
        packages =
          pkgs.lib.getAttrs (builtins.attrNames localPackagesQuery) scope;
      in
      {
        legacyPackages = scope;

        packages = packages // { default = packages.cooltt; };

        devShells.default = pkgs.mkShell {
          inputsFrom = builtins.attrValues packages;
          buildInputs = devPackages ++ [
            pkgs.fd
            pkgs.nixpkgs-fmt
            pkgs.pkg-config
            pkgs.shellcheck
          ];
        };
      });
}
