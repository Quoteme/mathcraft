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
            pkgs.libx11
            pkgs.libxcursor
            pkgs.libxext
            pkgs.libxfixes
            pkgs.libxi
            pkgs.libxinerama
            pkgs.libxrandr
            pkgs.libxrender
            pkgs.xorgproto
          ];
          extraOutputsToInstall = [ "dev" ];
        };
        # GLFW and raylib load these with dlopen at runtime.
        runtimeLibs = with pkgs; [
          libGL
          libx11
          libxcursor
          libxext
          libxfixes
          libxi
          libxinerama
          libxrandr
          libxrender
        ];
      in
      {
        devShell = pkgs.mkShell {
          name = "lean4";
          nativeBuildInputs = with pkgs; [
            cmake
            curl
            elan
            git
            ninja
            pkg-config
          ];
          buildInputs = runtimeLibs ++ [ pkgs.xorgproto pkgs.zlib ];
          LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath runtimeLibs;
          # raylib's bundled CMake files predate the minimum CMake 4 accepts.
          CMAKE_POLICY_VERSION_MINIMUM = "3.5";
        };
      }
    );
}
