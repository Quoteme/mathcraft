# MathCraft

Minecraft written in Lean4.

## Building

Enter the development shell first, it provides `elan`, `cmake` and the X11/OpenGL
libraries:

```bash
nix develop
```

On a fresh checkout, fetch the dependencies and patch Raylib.lean, whose
`toolchain-4.4.0` branch does not compile on this project's toolchain as is:

```bash
lake update raylib
git -C .lake/packages/raylib apply ../../../patches/raylib-lean-4.6.patch
```

Use `lake update raylib` rather than a bare `lake update`: Mathlib has no pinned
revision in `lakefile.lean`, so a bare update would move it to current master.

```bash
lake build
```

Lake caches dependency lakefiles without their options, so after changing the
options of a `require`, rebuild once with `lake -R build`.

## Running

```bash
./.lake/build/bin/mathcraft
```
