import Mathlib
import KP.Basic.CERT_Arb
-- KP/Basic/D5.lean
-- D5: β > β₀ ⟹ w1(β) < 1/7  (KP smallness condition)
-- David Fox | Theorema Aureum 143 | 2026-06-14
--
-- HONESTY HEADER
-- Status: bracket + arithmetic fully proved.
--         D5_transfer takes two explicit OPEN Prop parameters (not axioms).
-- Axiom footprint: {propext, Classical.choice, Quot.sound}
-- sorry: 0 | axiom: 0 | native_decide: 0
--
-- The KP (Kotecký–Preiss) entropy threshold for SU(3) lattice gauge:
--   Condition: w1(β) < 1/7   where w1(β) = exp(−β)·w1_poly_rat(β)
-- For β > β₀ ≈ 2.0794 this holds, but the proof requires:
--   (a) w1(β₀) < 1/7        — from SU(3) Haar integration, OPEN in Lean
--   (b) w1 is nonincreasing  — from Laplace monotonicity, OPEN in Lean
-- Both are labelled Prop parameters in D5_transfer, NOT axioms.
-- Proves NOTHING new about the YM mass gap. Surface #1: OPEN.

namespace TheoremaAureum.KP

-- -------------------------------------------------------------------------
-- Rational arithmetic: beta0 bracket and KP threshold
-- -------------------------------------------------------------------------

lemma beta0_hi_lt_208 : beta0_hi < 208 / 100 := by simp [beta0_hi]; norm_num
lemma beta0_hi_gt_207 : 207 / 100 < beta0_hi := by simp [beta0_hi]; norm_num
lemma kp_geometric_ratio : 7 * ((1 : ℚ) / 7) = 1 := by norm_num
lemma kp_ratio_lt_one : (1 : ℚ) / 7 < 1 := by norm_num

lemma kp_convergence_from_smallness (w : ℚ) (hw : w < 1 / 7) (hw0 : 0 ≤ w) :
    7 * w < 1 := by linarith

-- Bracket consistency: 0 < beta0_lo < beta0_hi < 2.08.
lemma d5_bracket_valid :
    (0 : ℚ) < beta0_lo ∧ beta0_lo < beta0_hi ∧ beta0_hi < 208 / 100 :=
  ⟨beta0_lo_pos, beta0_bracket, beta0_hi_lt_208⟩

-- -------------------------------------------------------------------------
-- D5_transfer: β > β₀ ⟹ w1(β) < 1/7
--
-- Two explicit OPEN Prop parameters (not axioms):
--   hw1_lo  : w1(beta0_lo) < 1/7  (Haar integration, absent from mathlib)
--   hw1_dec : w1 is nonincreasing past beta0_lo  (Laplace, absent from mathlib)
--
-- Proof is immediate: hw1_dec β gives w1(β) ≤ w1(beta0_lo) < 1/7.
-- -------------------------------------------------------------------------
theorem D5_transfer
    (β : ℚ)
    (hβ : beta0_lo < β)
    -- OPEN — requires SU(3) Haar: w1 at beta0_lo is already below 1/7
    (hw1_lo : Real.exp (-(beta0_lo : ℝ)) * (w1_poly_rat beta0_lo : ℝ) < 1 / 7)
    -- OPEN — requires Laplace monotonicity: w1 nonincreasing past beta0_lo
    (hw1_dec : ∀ γ : ℚ, beta0_lo ≤ γ →
        Real.exp (-(γ : ℝ)) * (w1_poly_rat γ : ℝ) ≤
        Real.exp (-(beta0_lo : ℝ)) * (w1_poly_rat beta0_lo : ℝ)) :
    Real.exp (-(β : ℝ)) * (w1_poly_rat β : ℝ) < 1 / 7 :=
  lt_of_le_of_lt (hw1_dec β (le_of_lt hβ)) hw1_lo

end TheoremaAureum.KP
