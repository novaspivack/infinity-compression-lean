import Lake
open Lake DSL

package «infinity-compression» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc6"

@[default_target]
lean_lib «InfinityCompression» where
  roots := #[`InfinityCompression]
