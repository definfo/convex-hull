{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-compat = {
      url = "github:roberth/flake-compat?rev=9680a5107f974df5a01d7fcd77a1ebe90cf5a8ee";
      flake = false;
    };
    flake-parts = {
      url = "github:hercules-ci/flake-parts";
      inputs.nixpkgs-lib.follows = "nixpkgs";
    };
  };

  outputs =
    inputs@{
      self,
      nixpkgs,
      flake-compat,
      flake-parts,
    }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = inputs.nixpkgs.lib.systems.flakeExposed;

      perSystem =
        {
          pkgs,
          system,
          ...
        }:
        {
          _module.args.pkgs = import inputs.nixpkgs {
            inherit system;
            overlays = [
              (_final: prev: {
                coqPackages = prev.coqPackages_8_20;
              })
            ];
          };

          devShells.default = pkgs.mkShell {
            strictDeps = true;

            nativeBuildInputs =
              with pkgs.coqPackages;
              [
                coq
                coq-lsp
                vsrocq-language-server # For coq.version <= 8.15, use Vscoq legacy
              ]
              ++ [
                pkgs.python314
                pkgs.clang-tools
              ];

            env = {
              MAKEFLAGS = "-j8";
            };
          };
        };
    };
}
