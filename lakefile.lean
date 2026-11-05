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

-- `main` needs a much newer toolchain than this project uses.
-- `cc` is set so that Lean's clang headers are not passed to the system compiler.
require raylib from git
  "https://github.com/KislyjKisel/Raylib.lean" @ "toolchain-4.4.0"
    with NameMap.empty.insert `cc "cc"

lean_lib «Mathcraft» where
  -- add library configuration options here

@[default_target]
lean_exe «mathcraft» where
  root := `Main
  moreLinkArgs := #["-L.lake/packages/raylib/raylib/build/raylib", "-lraylib"]
