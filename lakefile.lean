import Lake
open Lake DSL

package «mathcraft» where
  -- add package configuration options here

  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «Mathcraft» where
  -- add library configuration options here

@[default_target]
lean_exe «mathcraft» where
  root := `Main
