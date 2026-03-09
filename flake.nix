{
  description = "A Nix-flake-based Rocq(Coq) development environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-parts = {
      url = "github:hercules-ci/flake-parts";
      inputs.nixpkgs-lib.follows = "nixpkgs";
    };
  };

  outputs =
    inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "aarch64-darwin"
        "x86_64-darwin"
      ];

      perSystem =
        {
          config,
          pkgs,
          lib,
          ...
        }:
        let
          coqVersion = "8.15"; # Change this value to update the whole stack
          # coqVersion = "8.20";
          coqPackages = pkgs."coqPackages_${lib.versions.major coqVersion}_${lib.versions.minor coqVersion}";
        in
        {
          devShells.default = pkgs.mkShell {
            packages =
              with coqPackages;
              [
                coq
                # For coq.version <= 8.15, use legacy Vscoq version instead
                # coq-lsp
              ];
          };
        };
    };
}
