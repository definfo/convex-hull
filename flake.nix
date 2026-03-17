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
      ];

      perSystem =
        {
          pkgs,
          lib,
          system,
          ...
        }:
        let
          coqVersion = builtins.head (builtins.split "\n" (builtins.readFile ./.coq-version));
        in
        {
          _module.args.pkgs = import inputs.nixpkgs {
            inherit system;
            overlays = [
              (_final: _prev: {
                coqPackages = _prev."coqPackages_${lib.versions.major coqVersion}_${lib.versions.minor coqVersion}";
              })
            ];
          };

          devShells.default = pkgs.mkShell {
            packages =
              with pkgs.coqPackages;
              [
                coq
                coq-lsp
                # NOTE: For coq.version <= 8.15, use Vscoq legacy
                vsrocq-language-server
              ];
          };
        };
    };
}
