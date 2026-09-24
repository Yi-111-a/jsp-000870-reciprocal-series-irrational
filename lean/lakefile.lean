import Lake
open Lake DSL

package «jsp870» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0"

@[default_target]
lean_lib «JSP870» where
  globs := #[.submodules `JSP870]
