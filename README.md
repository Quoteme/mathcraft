# MathCraft

Minecraft written in Lean4.

## Compilation

Everything runs inside the Nix development shell, which provides `elan`, `cmake`
and the X11/OpenGL libraries:

```bash
nix develop
```

On a fresh checkout, fetch the dependencies and patch Raylib.lean for this
project's Lean version:

```bash
lake update raylib
git -C .lake/packages/raylib apply ../../../patches/raylib-lean-4.6.patch
```

Then build:

```bash
lake build
```

Avoid a bare `lake update`, it would move Mathlib to current master. After
changing the options of a `require`, rebuild once with `lake -R build`.

## Usage

Start the game from inside the development shell:

```bash
lake exe mathcraft
```

The window lists the worlds in `<cwd>/library`, one subfolder per world, and
creates the folder if it doesn't exist. To load another folder, change the path
and click **Load**. **New world** adds a world to the current folder. Scroll with
the mouse wheel if the list doesn't fit.
