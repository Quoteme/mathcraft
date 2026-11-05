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
        fhs = pkgs.buildFHSUserEnv {
          name = "lean4";
          targetPkgs = pkgs: with pkgs; [
            pkgs.curl
            pkgs.git
            pkgs.cmake
            pkgs.gcc
            pkgs.ninja
            pkgs.zlib
            pkgs.elan

            # raylib: build tooling and X11/OpenGL headers and libraries
            pkgs.pkg-config
            pkgs.libGL
            pkgs.xorg.libX11
            pkgs.xorg.libXcursor
            pkgs.xorg.libXext
            pkgs.xorg.libXfixes
            pkgs.xorg.libXi
            pkgs.xorg.libXinerama
            pkgs.xorg.libXrandr
            pkgs.xorg.libXrender
            pkgs.xorg.xorgproto
          ];
          extraOutputsToInstall = [ "dev" ];
        };
      in
      {
        devShell = fhs.env;
      }
    );
}
