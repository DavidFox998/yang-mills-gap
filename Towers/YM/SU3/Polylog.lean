/-
  Towers/YM/SU3/Polylog.lean — Degree-4 polylogarithm bound (2026-06-15)

  ∑_{n≥0} (n+1)⁴·rⁿ ≤ 24/(1−r)⁵  for r ∈ [0, 1).

  Proof: (n+1)⁴ ≤ (n+1)(n+2)(n+3)(n+4) pointwise (since (n+2)(n+3)(n+4) ≥ (n+1)³),
  and ∑ (n+1)(n+2)(n+3)(n+4)·rⁿ = 24·∑ C(n+4,4)·rⁿ = 24/(1−r)⁵
  (from tsum_choose_mul_geometric_of_norm_lt_one 4).

  This closes Gap 2 in WeylUpperBound.lean.

  STATUS: SCAFFOLD — NOT a registered brick.
  YM Surface #1: OPEN.  No mass-gap claim.
-/
import Mathlib.Analysis.SpecificLimits.Basic

open Real

namespace SU3Polylog

/-- 24·C(k+4,4) = (k+1)(k+2)(k+3)(k+4). -/
private lemma choose_four_val (k : ℕ) :
    24 * (k + 4).choose 4 = (k + 1) * (k + 2) * (k + 3) * (k + 4) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (k + 4) 4
  simp [Nat.descFactorial, Nat.factorial] at h
  linarith [show (k + 4) * (k + 3) * (k + 2) * (k + 1) =
      (k + 1) * (k + 2) * (k + 3) * (k + 4) from by ring]

/-- **Gap 2 CLOSED (2026-06-15).**  ∑_{n≥0} (n+1)⁴·rⁿ ≤ 24/(1−r)⁵  for r ∈ [0, 1).

    Proof: (n+1)⁴ ≤ (n+1)(n+2)(n+3)(n+4) and ∑(n+1)…(n+4)·rⁿ = 24/(1−r)⁵. -/
lemma tsum_pow_four_mul_geometric_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' n : ℕ, ((n : ℝ) + 1) ^ 4 * r ^ n ≤ 24 / (1 - r) ^ 5 := by
  have hr_norm : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0]
  have hSk : ∀ j : ℕ, Summable (fun n : ℕ => (n : ℝ) ^ j * r ^ n) :=
    fun j => summable_pow_mul_geometric_of_norm_lt_one j hr_norm
  -- (n+1)⁴·rⁿ is summable
  have hLHS : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 4 * r ^ n) :=
    ((((hSk 4).add ((hSk 3).mul_left 4)).add
        (((hSk 2).mul_left 6).add (((hSk 1).mul_left 4).add (hSk 0))))).congr
      (fun n => by push_cast; ring)
  -- (n+1)(n+2)(n+3)(n+4)·rⁿ is summable  (n⁴ + 10n³ + 35n² + 50n + 24)
  have hRHS : Summable (fun n : ℕ =>
      ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 4) * r ^ n) :=
    ((((hSk 4).add ((hSk 3).mul_left 10)).add
        (((hSk 2).mul_left 35).add (((hSk 1).mul_left 50).add ((hSk 0).mul_left 24))))).congr
      (fun n => by push_cast; ring)
  -- Pointwise: (n+1)⁴ ≤ (n+1)(n+2)(n+3)(n+4) since (n+2)(n+3)(n+4) ≥ (n+1)³
  have hpoint : ∀ n : ℕ,
      ((n : ℝ) + 1) ^ 4 * r ^ n ≤
      ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 4) * r ^ n :=
    fun n => mul_le_mul_of_nonneg_right
      (by nlinarith [Nat.cast_nonneg (α := ℝ) n]) (pow_nonneg hr0 n)
  -- ∑(n+1)(n+2)(n+3)(n+4)·rⁿ = 24·∑ C(n+4,4)·rⁿ = 24/(1−r)⁵
  have hrhs_eq : ∑' n : ℕ,
      ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 4) * r ^ n =
      24 / (1 - r) ^ 5 := by
    have hgen := tsum_choose_mul_geometric_of_norm_lt_one 4 hr_norm
    have heq : ∀ n : ℕ,
        ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 4) * r ^ n =
        24 * ((n + 4).choose 4 : ℝ) * r ^ n := fun n => by
      have h4 : ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 4) =
          (24 : ℝ) * ((n + 4).choose 4 : ℝ) := by
        exact_mod_cast (choose_four_val n).symm
      rw [h4]
    simp_rw [heq,
      show ∀ n : ℕ, (24 : ℝ) * ((n + 4).choose 4 : ℝ) * r ^ n =
          24 * (((n + 4).choose 4 : ℝ) * r ^ n) from fun n => by ring]
    rw [tsum_mul_left (a := (24 : ℝ)), hgen]
    ring
  calc ∑' n : ℕ, ((n : ℝ) + 1) ^ 4 * r ^ n
      ≤ ∑' n : ℕ,
          ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 4) * r ^ n :=
        tsum_le_tsum hpoint hLHS hRHS
    _ = 24 / (1 - r) ^ 5 := hrhs_eq

end SU3Polylog
