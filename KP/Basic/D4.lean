import Mathlib
import KP.Basic.CERT_Arb
-- KP/Basic/D4.lean
-- D4: w1(0.86) > 1/7  (D4 criterion FAILS at β=0.86 — certified negative)
-- David Fox | Theorema Aureum 143 | 2026-06-14
--
-- HONESTY HEADER
-- Status: fully proved. Zero sorry. Zero axiom. Zero native_decide.
-- Axiom footprint: {propext, Classical.choice, Quot.sound}
--
-- What this proves: at β = 0.86, the SU(3) single-site KP weight
--   w1(β) = exp(-β) · w1_poly_rat(β)
-- exceeds the KP entropy threshold 1/7.  The D4 criterion therefore
-- FAILS at β = 0.86 — cluster-expansion convergence is not certified
-- at this coupling.  This is NOT a mass-gap result; it certifies
-- divergence at one sub-threshold coupling.  Surface #1: OPEN.

namespace TheoremaAureum.KP

-- -------------------------------------------------------------------------
-- Cast helper: w1_poly_rat(0.86) as a real number equals the exact ℚ value.
-- -------------------------------------------------------------------------
private lemma w1_poly_086_real :
    (w1_poly_rat (86 / 100) : ℝ) = 53629810274551837 / 52488000000000000 := by
  simp only [w1_poly_rat, m0, m2, m3, m4, m5, m6]
  push_cast
  norm_num

-- -------------------------------------------------------------------------
-- w1_full_086: the real-valued w1 single-site weight at β = 0.86.
-- w1(β) = exp(-β) · (inner partial sum)
-- -------------------------------------------------------------------------
noncomputable def w1_full_086 : ℝ :=
  Real.exp (-(86 : ℝ) / 100) * (w1_poly_rat (86 / 100) : ℝ)

lemma w1_full_086_pos : (0 : ℝ) < w1_full_086 :=
  mul_pos (Real.exp_pos _) (by rw [w1_poly_086_real]; norm_num)

-- w1(0.86) < 7 — exp(-0.86) ≤ 1 and inner sum ≈ 1.022 < 7.
lemma w1_full_086_lt_seven : w1_full_086 < 7 := by
  unfold w1_full_086
  rw [w1_poly_086_real]
  have hexp_le : Real.exp (-(86 : ℝ) / 100) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by norm_num)
  have hpoly_pos : (0 : ℝ) ≤ 53629810274551837 / 52488000000000000 := by norm_num
  have hle := mul_le_mul_of_nonneg_right hexp_le hpoly_pos
  simp only [one_mul] at hle
  linarith [show (53629810274551837 : ℝ) / 52488000000000000 < 7 by norm_num]

-- -------------------------------------------------------------------------
-- D4_fail: w1(0.86) > 1/7.
-- The D4 entropy criterion is EXCEEDED at β = 0.86.
-- -------------------------------------------------------------------------
theorem D4_fail :
    (1 : ℝ) / 7 < Real.exp (-(86 : ℝ) / 100) * (w1_poly_rat (86 / 100) : ℝ) := by
  have h1 := exp_neg_086_lower    -- 422/1000 < exp(-0.86)
  rw [w1_poly_086_real]
  have hpos : (0 : ℝ) < 53629810274551837 / 52488000000000000 := by norm_num
  linarith [mul_lt_mul_of_pos_right h1 hpos,
            show (1 : ℝ) / 7 < 422 / 1000 * (53629810274551837 / 52488000000000000) by norm_num]

end TheoremaAureum.KP
