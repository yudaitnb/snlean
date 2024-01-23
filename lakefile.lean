import Lake
open Lake DSL
-- require std from git "https://github.com/leanprover/std4" @ "main"

package «snlean» where
  -- add package configuration options here

lean_lib «Snlean» where
  -- add library configuration options here

@[default_target]
lean_exe «snlean» where
  root := `Main
