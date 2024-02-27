{
  description = "Minecraft written in Lean4";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-utils = {
      inputs.nixpkgs.follows = "nixpkgs";
      url = "github:numtide/flake-utils";
    };
    lean4.url = "github:leanprover/lean4";
  };

  outputs = { self, nixpkgs, flake-utils, lean4 }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };
      in
      {
        devShell = pkgs.buildFHSUserEnv {
          name = "lean4";
          targetPkgs = pkgs: with pkgs; [
            pkgs.curl
            pkgs.git
            pkgs.cmake
            pkgs.gcc
            pkgs.lean4
            pkgs.ninja
            pkgs.zlib
            pkgs.elan
          ];
        };
      }
    );
}
