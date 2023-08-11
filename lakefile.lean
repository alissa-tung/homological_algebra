import Lake
open Lake DSL

package «homological_algebra» {
  -- add package configuration options here
}

@[default_target]
lean_lib «HomologicalAlgebra» {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
