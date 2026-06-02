import Lake
open Lake DSL

package internship where
  leanOptions := #[]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"

@[default_target]
lean_lib Internship where
  srcDir := "."
