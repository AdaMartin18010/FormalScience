import Lake
open Lake DSL

package «formalre» {
  -- Package configuration
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «FormalRE» {
  roots := #[`FormalRE]
  globs := #[Glob.submodules `FormalRE]
}
