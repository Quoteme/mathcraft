{
  description = "Minecraft written in Lean4";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-utils = {
      inputs.nixpkgs.follows = "nixpkgs";
      url = "github:numtide/flake-utils";
    };
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };
      in
      {
        devShells.default = pkgs.mkShell.override
          {
            stdenv = pkgs.pkgs.clangStdenv;
          }
          {
            buildInputs = with pkgs; [
              cmake-language-server
              lean4
              unixtools.whereis
              git
              cmake
              xorg.libX11
              xorg.libXrandr
              xorg.libXinerama
              xorg.libXcursor
              xorg.libXi
              libGL
              raylib
              # Here I tried adding libX11 manually, which did not work :(
              # (lean4.overrideAttrs
              #   (new: old: {
              #     buildInputs = old.buildInputs ++ [
              #       xorg.libX11
              #     ];
              #   })
              # )
            ];
          };
      }
    );
}
