import Lake
open Lake DSL

package «mathcraft» where
  -- add package configuration options here

lean_lib «Mathcraft» where
  -- add library configuration options here

@[default_target]
lean_exe «mathcraft» where
  root := `Main
