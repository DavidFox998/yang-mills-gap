import Lake
open Lake DSL

package «yang-mills-gap» where
  name := "yang-mills-gap"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.12.0"

lean_lib Towers where
  roots := #[`Towers]

lean_lib KP where
  roots := #[`KP]
