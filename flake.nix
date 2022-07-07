{
  description = "Experimental implementation of Cartesian cubical type theory";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-22.05";
    flake-utils.url = "github:numtide/flake-utils";

    opam-repository = {
      url = "github:ocaml/opam-repository";
      flake = false;
    };
    
    opam-nix = {
      url = "github:tweag/opam-nix";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-utils.follows = "flake-utils";
      inputs.opam-repository.follows = "opam-repository";
    };
  };

  outputs = { self
            , flake-utils
            , opam-nix
            , nixpkgs
            , opam-repository
            }@inputs:
    flake-utils.lib.eachDefaultSystem (system: {
      legacyPackages = let
        on = opam-nix.lib.${system};
      in on.buildDuneProject { } "cooltt" ./. {
        ocaml-base-compiler = null;
      };

      defaultPackage = self.legacyPackages.${system}."cooltt";
    });
}
