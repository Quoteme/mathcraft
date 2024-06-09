import Lake
open Lake DSL

package «mathcraft» where
  -- add package configuration options here

  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.7.0"


require raylib from git
  "https://github.com/KislyjKisel/Raylib.lean" @ "main"

lean_lib «Mathcraft» where
  -- add library configuration options here

@[default_target]
lean_exe «mathcraft» where
  root := `Main
  moreLinkArgs := #["-Llake-packages/raylib/raylib/build/raylib", "-lraylib"]
