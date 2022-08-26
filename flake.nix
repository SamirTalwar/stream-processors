{
  description = "stream-processors";

  inputs = {
    nixpkgs = {
      # last known version of nixpkgs that has a working Agda build on aarch64
      url = github:NixOS/nixpkgs/6fcc9f249f38178ca29cd719dba9b2e62af41c89;
    };

    flake-utils = {
      url = github:numtide/flake-utils;
    };
  };

  outputs =
    { self
    , nixpkgs
    , flake-utils
    }:
    flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs { inherit system; };
    in
    rec {
      formatter = pkgs.nixpkgs-fmt;

      devShells.default = with pkgs; mkShell {
        buildInputs = [
          (agda.withPackages (ps: [
            ps.standard-library
          ]))
        ];
      };
    }
    );
}
