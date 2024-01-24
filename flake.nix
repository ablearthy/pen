{
  description = "Description";

  inputs = {
    # nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    vscoq.url = "github:ablearthy/vscoq";
    vscoq.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { self, nixpkgs, vscoq, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        devTools = with pkgs; [
          bashInteractive
          
          coqPackages.coq
          coqPackages.mathcomp-ssreflect

          vscoq.packages.${system}.vscoq-language-server
        ];
      in {
        devShell = pkgs.mkShell ({
          buildInputs = devTools;
        });
      }
    );
}
