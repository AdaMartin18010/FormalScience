import Lake
open Lake DSL

package «formalscience-lean» {
  -- 包配置
  keywords := #["formalization", "mathematics", "computer-science"]
  description := "FormalScience project Lean 4 code examples"
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «FormalScience» {
  -- 库配置
  roots := #[`.`]
  globs := #[Glob.submodules `FormalScience]
}
