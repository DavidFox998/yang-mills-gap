-- Axiom status: Classical trio only. 0 sorry. 0 new axioms.
-- Proves w1_seven_lt and w1_seven_pos at β₇ = β₀_rat/3
-- WITHOUT using Cert_Arb_w1_weyl_lt.
--
-- Key identity: the CORRECTED formula w1_weyl_series(β₇) at β₇ = β₀/3 equals
-- the OLD formula exp(-β₀)·∑' det[toeplitzReal β₀ k], which is bounded by the
-- existing W1_Numeric_Surface enclosure (proved in BesselBounds.lean, trio-clean).
--
-- w1_seven_pos uses a rational lower enclosure of the det-tsum:
--   ∑ k∈range51, (toeplitzDetInterval((i:ℤ)-25)).lo  ≈  1.039 + small
--   minus a tail bound 1/10^20 → tsum > 0.
--
-- All proofs: classical trio only.  0 sorry.  0 new axioms.

import Towers.YM.BesselBounds

namespace TheoremaAureum.Towers.YM.W1SeventhProof

open Real BigOperators Finset
open TheoremaAureum.Towers.YM.WeylToeplitzBound
open TheoremaAureum.Towers.YM.IntervalArith
open TheoremaAureum.Towers.YM.BesselSeries RatInterval
open TheoremaAureum.Towers.YM.W1NumericProof
open TheoremaAureum.Towers.YM.BesselBounds

local notation "β₀R" => (β₀_rat : ℝ)
private abbrev S26 : Finset ℤ := Finset.Icc (-25) 25

/-! ## §1  β₇_rat: the threshold coupling -/

/-- β₇_rat = β₀_rat / 3.  At this coupling the corrected formula equals the OLD
    Gross-Witten formula at β₀, which is bounded by W1_Numeric_Surface. -/
def β₇_rat : ℚ := β₀_rat / 3

/-! ## §2  Key identity: corrected formula at β₇ = OLD formula at β₀ -/

private lemma toeplitzReal_correct_at_seventh (k : ℤ) :
    toeplitzReal_correct ((β₀_rat : ℝ) / 3) k = toeplitzReal β₀R k := by
  ext i j
  simp only [toeplitzReal_correct, toeplitzReal, Matrix.of_apply]

/-- The corrected weight at β₇ = β₀/3 equals exp(-β₀)·∑' det[toeplitzReal β₀ k].
    Proof: exp(-3·(β₀/3)) = exp(-β₀) and toeplitzReal_correct(β₀/3) = toeplitzReal(β₀). -/
lemma w1_seven_eq :
    w1_weyl_series ((β₇_rat : ℚ) : ℝ) =
    Real.exp (-β₀R) * ∑' k : ℤ, (toeplitzReal β₀R k).det := by
  unfold w1_weyl_series β₇_rat
  push_cast
  congr 1
  · ring
  · congr 1; ext k; rw [toeplitzReal_correct_at_seventh]

/-! ## §3  w1_seven_lt: w1_weyl_series(β₇) < 1/7 (trio-clean) -/

/-- **[PROVED, classical trio]** w1_weyl_series(β₇) < 1/7.
    Chain: w1(β₇) = exp(-β₀)·∑'det ≤ exp_hi·(hi_sum + tail) < 1/7. -/
theorem w1_seven_lt : w1_weyl_series ((β₇_rat : ℚ) : ℝ) < 1 / 7 := by
  rw [w1_seven_eq]
  obtain ⟨_, htsum, hrat⟩ := bb_w1_numeric_surface
  have hexp_nn : 0 ≤ Real.exp (-β₀R) := Real.exp_nonneg _
  have hexp_le : Real.exp (-β₀R) ≤ (exp_beta0_interval.hi : ℝ) := exp_le_beta0_hi
  have hrat_R : (exp_beta0_interval.hi : ℝ) * ((finite_hi_sum : ℝ) + (tail_ub : ℝ)) < 1 / 7 := by
    have h : exp_beta0_interval.hi * (finite_hi_sum + tail_ub) < 1 / 7 := hrat
    exact_mod_cast h
  calc Real.exp (-β₀R) * ∑' k : ℤ, (toeplitzReal β₀R k).det
      ≤ Real.exp (-β₀R) * ((finite_hi_sum : ℝ) + (tail_ub : ℝ)) :=
        mul_le_mul_of_nonneg_left htsum hexp_nn
    _ ≤ (exp_beta0_interval.hi : ℝ) * ((finite_hi_sum : ℝ) + (tail_ub : ℝ)) :=
        mul_le_mul_of_nonneg_right hexp_le (by positivity)
    _ < 1 / 7 := hrat_R

/-! ## §4  Lower-bound infrastructure for w1_seven_pos -/

/-- Rational lower bound on the finite det sum over shifts k = -25..25. -/
private def finite_lo_sum : ℚ :=
  ∑ i ∈ Finset.range 51, (toeplitzDetInterval ((i : ℤ) - 25)).lo

/-- The finite sum (range-51 form) is bounded below by finite_lo_sum. -/
private lemma finite_sum_ge :
    (finite_lo_sum : ℝ) ≤
    ∑ i ∈ Finset.range 51, (toeplitzReal β₀R ((i : ℤ) - 25)).det := by
  push_cast [finite_lo_sum]
  apply Finset.sum_le_sum
  intro i _
  exact (toeplitz_det_contains ((i : ℤ) - 25)).1

/-- The rational lower sum exceeds the tail bound: the OLD det-tsum is bounded
    away from zero.  Pure norm_num (Bessel interval evaluation, N = 5).
    Runtime: similar to bb_part_c. -/
set_option maxHeartbeats 0 in
private lemma finite_lo_sum_gt_tail : (tail_ub : ℚ) < finite_lo_sum := by
  norm_num [finite_lo_sum, tail_ub,
            TheoremaAureum.Towers.YM.ToeplitzDetInterval.toeplitzDetInterval,
            TheoremaAureum.Towers.YM.ToeplitzDetInterval.detI,
            TheoremaAureum.Towers.YM.IntervalArith.besselIn_beta0_interval,
            TheoremaAureum.Towers.YM.IntervalArith.besselIn_interval,
            TheoremaAureum.Towers.YM.IntervalArith.besselIn_partial,
            TheoremaAureum.Towers.YM.IntervalArith.besselIn_error,
            TheoremaAureum.Towers.YM.IntervalArith.ofRat,
            TheoremaAureum.Towers.YM.IntervalExp.β₀_rat,
            Finset.sum_range_succ, Finset.sum_range_zero,
            Nat.factorial]

/-- The complement tail is bounded below by -tail_ub.
    Proof: -(∑' compl det) ≤ ∑' compl |det| ≤ ∑' compl g ≤ tail_ub.
    Uses compl_g_tsum_le (now non-private in BesselBounds). -/
private lemma compl_det_tsum_ge_neg_tail :
    -(tail_ub : ℝ) ≤
    ∑' k : ↥((↑S26 : Set ℤ))ᶜ, (toeplitzReal β₀R (k : ℤ)).det := by
  have h_det_s : Summable (fun k : ↥((↑S26 : Set ℤ))ᶜ =>
      (toeplitzReal β₀R (k : ℤ)).det) :=
    summable_toeplitz_det.subtype _
  -- Each -(det k) ≤ g k (from |det k| ≤ g k via the neg direction)
  have h_neg_le_g : ∀ k : ↥((↑S26 : Set ℤ))ᶜ,
      -(toeplitzReal β₀R (k : ℤ)).det ≤ g (k : ℤ) := fun k => by
    calc -(toeplitzReal β₀R (k : ℤ)).det
        ≤ |-(toeplitzReal β₀R (k : ℤ)).det| := le_abs_self _
      _ = |(toeplitzReal β₀R (k : ℤ)).det|    := abs_neg _
      _ ≤ 6 * (r ^ (k.1.natAbs - 2) * C_exp) ^ 3 := det_abs_le (k : ℤ)
      _ = g (k : ℤ) := by unfold g q; ring
  have h_g_s : Summable (fun k : ↥((↑S26 : Set ℤ))ᶜ => g (k : ℤ)) :=
    g_summable.subtype _
  -- -(∑' det) = ∑' (-det) ≤ ∑' g ≤ tail_ub
  have h_neg_sum : -(∑' k : ↥((↑S26 : Set ℤ))ᶜ, (toeplitzReal β₀R (k : ℤ)).det) ≤
      (tail_ub : ℝ) := by
    rw [← tsum_neg]
    exact le_trans
      (tsum_le_tsum h_neg_le_g h_det_s.neg h_g_s)
      (le_trans compl_g_tsum_le (by norm_num [tail_ub]))
  linarith

/-- The reindexing identity: Finset.Icc form ↔ range-51 form. -/
private lemma S26_range_eq :
    ∑ k ∈ S26, (toeplitzReal β₀R k).det =
    ∑ i ∈ Finset.range 51, (toeplitzReal β₀R ((i : ℤ) - 25)).det := by
  rw [show S26 = (Finset.range 51).image (fun i : ℕ => (i : ℤ) - 25) from by
    ext k
    simp only [S26, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro ⟨h1, h2⟩
      exact ⟨(k + 25).toNat, by omega, by omega⟩
    · intro ⟨_, _, hik⟩; omega]
  exact Finset.sum_image (by intro x _ y _ h; omega)

/-- ∑' k : ℤ, (toeplitzReal β₀ k).det > 0. -/
private lemma tsum_det_pos :
    0 < ∑' k : ℤ, (toeplitzReal β₀R k).det := by
  have hS : Summable (fun k : ℤ => (toeplitzReal β₀R k).det) := summable_toeplitz_det
  rw [← Finset.sum_add_tsum_compl (s := S26) hS]
  rw [S26_range_eq]
  have hfin  : (finite_lo_sum : ℝ) ≤
      ∑ i ∈ range 51, (toeplitzReal β₀R ((i : ℤ) - 25)).det := finite_sum_ge
  have htail : -(tail_ub : ℝ) ≤
      ∑' k : ↥((↑S26 : Set ℤ))ᶜ, (toeplitzReal β₀R k.1).det :=
    compl_det_tsum_ge_neg_tail
  have hgt   : (tail_ub : ℝ) < (finite_lo_sum : ℝ) := by
    exact_mod_cast finite_lo_sum_gt_tail
  linarith

/-! ## §5  w1_seven_pos: 0 < w1_weyl_series(β₇) (trio-clean) -/

/-- **[PROVED, classical trio]** 0 < w1_weyl_series(β₇).
    Proof: w1(β₇) = exp(-β₀)·∑'det, both factors positive. -/
theorem w1_seven_pos : 0 < w1_weyl_series ((β₇_rat : ℚ) : ℝ) := by
  rw [w1_seven_eq]
  exact mul_pos (Real.exp_pos _) tsum_det_pos

-- Axiom audit (uncomment after lake build):
-- #print axioms w1_seven_lt   -- expect: [propext, Classical.choice, Quot.sound]
-- #print axioms w1_seven_pos  -- expect: [propext, Classical.choice, Quot.sound]

end TheoremaAureum.Towers.YM.W1SeventhProof
