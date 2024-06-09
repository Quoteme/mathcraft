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
          nativeBuildInputs = with pkgs; [
            pkg-config
            cmake
            clang
            gcc
            ninja
            zlib
          ];
          targetPkgs = pkgs: with pkgs; [
            curl
            git
            cmake
            xorg.libX11
            gcc
            clang
            lean4
            ninja
            zlib
            elan
          ];
        };
      }
    );
}
