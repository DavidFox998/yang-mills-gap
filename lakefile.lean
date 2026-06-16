import Lake
open Lake DSL

package «yang-mills-gap» where

-- SU(3) Yang-Mills tower — Morning Star Project
-- Lean 4 v4.12.0 | Mathlib v4.12.0 (commit 809c3fb3)
-- Axiom footprint: {propext, Classical.choice, Quot.sound}
-- sorry: 0 | sorryAx: 0 | native_decide: 0
--
-- KP cluster-expansion chain:
--   D4: w1(0.86) > 1/7                 (norm_num)
--   D5: beta > beta_0 => KP-smallness  (bracket arithmetic)
--   D6: N=36 tail certificate           (interval arithmetic)
--
-- YM wall infrastructure:
--   SU3Instances: haarSU3 Haar measure stack
--   WilsonPositivity: action >= 0, > 0 off vacuum
--   PeterWeylHeatVaradhan: heat-kernel envelope
--   VaradhanStripWidened: strip bound [1/200, 200]
--   SU3/W1: w1_poly_rat + bridge
--   SU3/WeylUpperBound: K(t) <= 96A/t^4
--   SU3/Tauberian: Wall 256.2b Tauberian chain
--
-- Clay YM target: Delta = inf spec(H) - E_0 >= m > 0

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.12.0"

@[default_target]
lean_lib YangMillsGap where
  roots := #[
    `YangMillsGap.KP.Basic.CERT_Arb,
    `YangMillsGap.KP.Basic.D4,
    `YangMillsGap.KP.Basic.D5,
    `YangMillsGap.KP.Basic.D6,
    `YangMillsGap.KP.Main,
    `YangMillsGap.SU3Instances,
    `YangMillsGap.WilsonPositivity,
    `YangMillsGap.PeterWeyl,
    `YangMillsGap.PeterWeylHeatVaradhan,
    `YangMillsGap.VaradhanStripWidened,
    `YangMillsGap.SU3.W1,
    `YangMillsGap.SU3.WeylUpperBound,
    `YangMillsGap.SU3.Tauberian,
    `YangMillsGap.SU3.Polylog
  ]
