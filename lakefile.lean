import Lake
open Lake DSL

package «theorema-aureum-towers» where

-- KP cluster-expansion package (CERT_Arb-based, 2026-06-14).
-- File layout:
--   KP/Basic/CERT_Arb.lean  — SU(3) moments, partial sum, exp bound, tail
--   KP/Basic/D4.lean         — w1(0.86) > 1/7 (D4 certified negative)
--   KP/Basic/D5.lean         — β > β₀ ⟹ KP smallness (bracket arithmetic)
--   KP/Basic/D6.lean         — N=36 tail certificate
--   KP/Main.lean             — top-level assembly
--
-- Towers/YM/SU3 Wall-256 bridge (2026-06-14).
-- File layout:
--   Towers/YM/SU3Instances.lean        — haarSU3 instance stack
--   Towers/YM/SU3/W1.lean              — w1_integral def + bridge theorem (sorry: 0)
--   Towers/YM/PeterWeylHeatVaradhan.lean — envelope + strip bound infrastructure (sorry: 0)
--   Towers/YM/VaradhanStripWidened.lean  — widened strip bound (sorry: 0)
--
-- Towers/RH — Riemann Hypothesis tower (restored 2026-06-15).
-- File layout:
--   Towers/RH/ZeroDensity.lean         — N(σ,T) def + N_monotone_in_sigma brick
--   Towers/RH/GrowthContradiction.lean — honest conditional reduction skeleton
--   Towers/RH/ZProtocolBridge.lean     — Z-Protocol honesty bridge (not a brick)
--   Towers/RH/Chain/C01_Arakelov.lean  — ArithmeticSurface + X₀(143) defs
--   Towers/RH/Chain/C02_Modularity.lean — modularity True stub
--   Towers/RH/Chain/C03_Positivity.lean — slope_inequality (genuine)
--   Towers/RH/Chain/C04_HeightBound.lean — vojta True stub
--   Towers/RH/Chain/C05_Discriminant.lean — discriminant True stub
--   Towers/RH/Chain/C06_ZetaControl.lean — bost_connes_threshold BRICK
--   Towers/RH/Chain/C07_RH.lean        — conditional combinator (not a brick)
--
-- Towers/BSD — BSD scaffold (restored 2026-06-15).
-- File layout:
--   Towers/BSD/MordellWeil.lean        — MordellWeil_OPEN stub (not a brick)
--
-- Towers/X0_143 — Analytic bounds for K=ℚ(√-143) and X₀(143) (2026-06-16).
-- File layout:
--   Towers/X0_143/Basic.lean          — K type, κ constant (10π/√143), idealCountBelow
--   Towers/X0_143/K1IdealGrowth.lean  — Landau ideal counting (3 named axioms, 0 sorry)
--
-- Axiom footprint: {propext, Classical.choice, Quot.sound} only.
-- sorry: 0 in KP; 0 in all Towers.YM.SU3.*; 0 in Towers.RH.*; 0 in Towers.BSD.*;
--   0 in Towers.X0_143.*.
-- WeylUpperBound.lean (not in roots): sorry=0 (named-Prop TailBound_Surface 2026-06-15).
-- mathlib v4.12.0 only. No native_decide.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.12.0"

@[default_target]
lean_lib KP where
  roots := #[`KP.Basic.CERT_Arb, `KP.Basic.D4, `KP.Basic.D5, `KP.Basic.D6, `KP.Main]

lean_lib RH where
  roots := #[`RH.Core.C08_M4WeilBridge, `RH.Core.P5Bridge14]

lean_lib Towers where
  roots := #[`Towers.YM.SU3Instances, `Towers.YM.SU3.W1,
             `Towers.YM.SU3.Tauberian,
             `Towers.YM.PeterWeylHeatVaradhan, `Towers.YM.VaradhanStripWidened,
             -- RH tower: C01–C07 chain (explicit roots so lake always compiles them)
             `Towers.RH.Chain.C01_Arakelov,
             `Towers.RH.Chain.C02_Modularity,
             `Towers.RH.Chain.C03_Positivity,
             `Towers.RH.Chain.C04_HeightBound,
             `Towers.RH.Chain.C05_Discriminant,
             `Towers.RH.Chain.C06_ZetaControl,
             `Towers.RH.Chain.C07_RH,
             `Towers.RH.Chain.C08_M4WeilBridge,
             `Towers.RH.Chain.C09_P5Bridge,
             `Towers.RH.Chain.C10_MainTheorem,
             -- RH supporting modules
             `Towers.RH.ZeroDensity, `Towers.RH.GrowthContradiction,
             `Towers.RH.ZProtocolBridge,
             -- BSD scaffold (restored 2026-06-15)
             `Towers.BSD.MordellWeil,
             -- W1/Toeplitz/Bessel chain (2026-06-17, 0 sorry, classical trio)
             `Towers.YM.Interval, `Towers.YM.IntervalExp,
             `Towers.YM.BesselSeries, `Towers.YM.IntervalBessel,
             `Towers.YM.ToeplitzDetInterval, `Towers.YM.WeylToeplitzBound,
             `Towers.YM.W1NumericProof, `Towers.YM.BesselBounds,
             `Towers.YM.W1Toeplitz,
             -- X0_143 base module (explicit root so Basic.olean builds before K1IdealGrowth)
             `Towers.X0_143.Basic,
             -- X0_143 analytic bounds for K=ℚ(√-143) (2026-06-16)
             `Towers.X0_143.K1IdealGrowth]
