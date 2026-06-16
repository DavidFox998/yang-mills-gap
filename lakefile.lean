import Lake
open Lake DSL

package yangMillsGap where
  name := "YangMillsGap"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "809c3fb3b5c8f5d7dace56e200b426187516535a"

lean_lib YangMillsGap where
  roots := #[`lean]

lean_lib TheoremaAureum where
  roots := #[`TheoremaAureum]
