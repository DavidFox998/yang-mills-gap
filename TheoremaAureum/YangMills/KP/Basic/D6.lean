import Mathlib
import KP.Basic.CERT_Arb
import KP.Basic.D4
-- KP/Basic/D6.lean
-- D6: KP_summable — the summability predicate and tail certificate
-- David Fox | Theorema Aureum 143 | 2026-06-14
--
-- HONESTY HEADER
-- Status: KP_summable fully defined; D6_holds_086 fully proved at fixed point.
--         D6_holds (general β > β₀) takes an explicit OPEN Prop parameter
--         for the w1 monotonicity condition (not an axiom).
-- Axiom footprint: {propext, Classical.choice, Quot.sound}
-- sorry: 0 here (sole sorry is tail_bound_086_le in CERT_Arb.lean)
-- axiom: 0 | native_decide: 0
--
-- KP_summable β states: the KP cluster-expansion certificate holds at β.
-- Two conditions (both ℚ-valued):
--   1. The inner partial sum > 1  (so the full w1 > exp(-β) > 0)
--   2. The N=36 tail bound < 1/7  (conservative rational constant)
-- Condition 2 is β-independent (tail_bound_N36 = 45/10^33 << 1/7).
-- Condition 1 requires w1_poly_rat β > 1 — proved at β = 86/100 via
-- w1_poly_rat_086_gt_one; for general β > β₀ it is a Prop parameter.
-- Proves NOTHING about the YM mass gap. Surface #1: OPEN.

namespace TheoremaAureum.KP

-- -------------------------------------------------------------------------
-- KP summability predicate
-- -------------------------------------------------------------------------
-- A sufficient certificate for KP cluster-expansion convergence:
--   · inner series > 1 at the given coupling (ensures w1 > 0)
--   · conservative N=36 tail bound is below 1/7
-- The tail condition is β-independent (tail_bound_N36 = 45/10^33).

def KP_summable (β : ℚ) : Prop :=
  (1 : ℚ) < w1_poly_rat β ∧ tail_bound_N36 < 1 / 7

-- -------------------------------------------------------------------------
-- D6 tail certificate: both conditions hold at β = 86/100  (no sorry)
-- -------------------------------------------------------------------------

-- Condition 1 at β = 86/100: w1_poly_rat(0.86) > 1.
lemma d6_partial_gt_one : (1 : ℚ) < w1_poly_rat (86 / 100) :=
  w1_poly_rat_086_gt_one

-- Condition 2: the conservative tail bound is always below 1/7.
lemma d6_tail_lt_threshold : tail_bound_N36 < 1 / 7 :=
  tail_bound_N36_lt_one_over_7

-- D6_holds at the certified point β = 86/100: fully proved, no sorry.
theorem D6_holds_086 : KP_summable (86 / 100) :=
  ⟨d6_partial_gt_one, d6_tail_lt_threshold⟩

-- -------------------------------------------------------------------------
-- D6_holds for general β > β₀
--
-- Requires one explicit OPEN Prop parameter:
--   hw1_mono : w1_poly_rat is increasing past beta0_lo
--              (from Weyl integration; absent from mathlib v4.12.0)
-- The tail condition is β-independent and fully proved.
-- -------------------------------------------------------------------------
theorem D6_holds
    (β : ℚ)
    (hβ : beta0_lo < β)
    -- OPEN — requires monotonicity of the inner series past beta0_lo
    (hw1_mono : (1 : ℚ) < w1_poly_rat β) :
    KP_summable β :=
  ⟨hw1_mono, tail_bound_N36_lt_one_over_7⟩

-- -------------------------------------------------------------------------
-- Supporting lemmas re-exported from CERT_Arb / D4
-- -------------------------------------------------------------------------

lemma d6_coeff_n0 : m0 / 1 = 1 := by simp [m0]
lemma d6_coeff_n2 : m2 / 2 = 1 / 4 := by norm_num [m2]
lemma d6_coeff_n4 : m4 / 24 = 1 / 32 := by norm_num [m4]
lemma d6_coeff_n6 : m6 / 720 = 13 / 4608 := by norm_num [m6]
lemma d6_m1_zero : m1 = 0 := by simp [m1]

lemma d6_tail_pos : (0 : ℚ) < tail_bound_N36 := tail_bound_N36_pos
lemma d6_tail_negligible : tail_bound_N36 < w1_poly_rat (86 / 100) - 1 / 7 := tail_negligible

-- Combined certificate theorem (no sorry in this section).
theorem d6_tail_certificate :
    (0 : ℚ) < tail_bound_N36 ∧
    tail_bound_N36 < 1 / 7 ∧
    tail_bound_N36 < w1_poly_rat (86 / 100) - 1 / 7 :=
  ⟨d6_tail_pos, d6_tail_lt_threshold, d6_tail_negligible⟩

theorem d6_moments_exact :
    m0 = 1 ∧ m1 = 0 ∧ m2 = 1/2 ∧ m3 = 1/4 ∧ m4 = 3/4 ∧ m5 = 15/16 ∧ m6 = 65/32 := by
  simp [m0, m1, m2, m3, m4, m5, m6]

theorem d6_partial_sum_exact :
    w1_poly_rat (86 / 100) = 53629810274551837 / 52488000000000000 :=
  w1_poly_rat_086

end TheoremaAureum.KP
