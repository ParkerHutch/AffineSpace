import Lake
open Lake DSL

package «Affine6501S24» where
  -- add package configuration options here

lean_lib «Affine6501S24» where
  -- add library configuration options here

@[default_target]
lean_exe «affine6501s24» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"