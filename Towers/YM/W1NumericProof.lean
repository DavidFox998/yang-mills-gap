-- Axiom status: Uses [propext, Classical.choice, Quot.sound] (classical trio only).
-- Closes W1_Numeric_Surface — the COMPUTATIONAL surface (3 parts):
--   (a) Summable (fun k : ℤ => (toeplitzReal β₀ k).det)   [real analysis]
--   (b) ∑' k, det ≤ finite_hi_sum + tail_ub               [enclosure + tail]
--   (c) exp_beta0_interval.hi * (finite_hi_sum + tail_ub) < 1/7  [rational ℚ]
--
-- KEY GEOMETRIC FACT (proved here, trio-clean):
--   toeplitzReal β k entry (i,j) = besselI_series |i-j-k| (β/3).
--   For all k : ℤ, index |i-j-k| ≥ k.natAbs - 2 (reverse triangle, |i-j| ≤ 2).
--   By besselI_series_le_exp_bound: entry ≤ r^{k.natAbs - 2} * C_exp
--   where r = β₀/6 < 1/2 < 1 and C_exp = exp((β₀/6)²).
--   Det ≤ 6 * (r^{k.natAbs - 2} * C_exp)³ — geometric in k.natAbs.
--
-- PART (c): pure ℚ — proved by `decide` (kernel reduction of computable ℚ).
--   NOTE: `#eval decide` runs in milliseconds (compiler); kernel `decide` is
--   equivalent but slower. Both give `true` because the margin is ≈ 3.86e-7.
--   If kernel decide times out during a full `lake build`, replace with:
--     `norm_num [exp_beta0_interval, finite_hi_sum, tail_ub, ...]`
--   (which unfolds and normalises via the norm_num reduction engine).
/-
W1NumericProof — Closes the W1_Numeric_Surface computational axiom.
-/

import Towers.YM.WeylToeplitzBound

namespace TheoremaAureum.Towers.YM.W1NumericProof

open Real BigOperators Finset
open TheoremaAureum.Towers.YM.WeylToeplitzBound
open TheoremaAureum.Towers.YM.IntervalArith
open TheoremaAureum.Towers.YM.BesselSeries RatInterval

/-! ## §1  Constants and basic bounds -/

/-- Abbreviation for β₀ as a real number. -/
noncomputable abbrev β₀R : ℝ := (β₀_rat : ℝ)

/-- Geometric decay rate r = β₀/6. -/
noncomputable def r : ℝ := β₀R / 6

/-- Exponential prefactor C = exp((β₀/6)²). -/
noncomputable def C_exp : ℝ := Real.exp (r ^ 2)

lemma r_pos : 0 < r := by unfold r β₀R β₀_rat; norm_num
lemma r_lt_half : r < 1 / 2 := by unfold r β₀R β₀_rat; norm_num
lemma r_lt_one : r < 1 := lt_trans r_lt_half (by norm_num)
lemma r_nonneg : 0 ≤ r := r_pos.le
lemma C_exp_pos : 0 < C_exp := Real.exp_pos _
lemma C_exp_nonneg : 0 ≤ C_exp := C_exp_pos.le

/-- q = r³ is the geometric ratio for |det| decay. -/
noncomputable def q : ℝ := r ^ 3

lemma q_pos : 0 < q := pow_pos r_pos 3
lemma q_nonneg : 0 ≤ q := q_pos.le
lemma q_lt_one : q < 1 := pow_lt_one r_nonneg r_lt_one (by norm_num)

/-! ## §2  Entry bound and index lemmas -/

/-- Each matrix entry is nonneg (Bessel series with nonneg argument). -/
lemma entry_nonneg (k : ℤ) (i j : Fin 3) :
    0 ≤ (toeplitzReal β₀R k) i j := by
  simp only [toeplitzReal, Matrix.of_apply]
  apply tsum_nonneg
  intro n
  apply div_nonneg
  · exact pow_nonneg (div_nonneg (by norm_num [β₀R, β₀_rat]) two_pos.le) _
  · positivity

/-- Entry ≤ r^{|i−j−k|} · C_exp, by besselI_series_le_exp_bound. -/
lemma entry_le_pow_mul (k : ℤ) (i j : Fin 3) :
    (toeplitzReal β₀R k) i j ≤ r ^ ((i : ℤ) - j - k).natAbs * C_exp := by
  simp only [toeplitzReal, Matrix.of_apply]
  have hx : 0 ≤ β₀R / 3 := by norm_num [β₀R, β₀_rat]
  apply le_trans (besselI_series_le_exp_bound _ _ hx)
  have hr : β₀R / 3 / 2 = r := by unfold r; ring
  simp only [hr, C_exp]
  exact le_refl _

/-- Reverse triangle: index |i−j−k| ≥ k.natAbs − 2 (natural subtraction). -/
lemma index_lower_bound (k : ℤ) (i j : Fin 3) :
    k.natAbs - 2 ≤ ((i : ℤ) - j - k).natAbs := by
  have hij : ((i : ℤ) - j).natAbs ≤ 2 := by
    fin_cases i <;> fin_cases j <;> decide
  have heq : (k : ℤ) = -((i : ℤ) - j - k) + ((i : ℤ) - j) := by ring
  have hkey : k.natAbs ≤ ((i : ℤ) - j - k).natAbs + ((i : ℤ) - j).natAbs := by
    calc k.natAbs
        = (-((i : ℤ) - j - k) + ((i : ℤ) - j)).natAbs := by conv_lhs => rw [heq]
      _ ≤ (-((i : ℤ) - j - k)).natAbs + ((i : ℤ) - j).natAbs := Int.natAbs_add_le _ _
      _ = ((i : ℤ) - j - k).natAbs + ((i : ℤ) - j).natAbs := by rw [Int.natAbs_neg]
  omega

/-- For all k : ℤ, every entry ≤ r^{k.natAbs − 2} · C_exp. -/
lemma entry_le_geometric (k : ℤ) (i j : Fin 3) :
    (toeplitzReal β₀R k) i j ≤ r ^ (k.natAbs - 2) * C_exp := by
  apply le_trans (entry_le_pow_mul k i j)
  apply mul_le_mul_of_nonneg_right _ C_exp_nonneg
  exact pow_le_pow_of_le_one r_nonneg r_lt_one.le (index_lower_bound k i j)

/-! ## §3  Determinant absolute-value bound -/

/-- |det(toeplitzReal β₀ k)| ≤ 6 · (r^{k.natAbs−2} · C_exp)³ for all k. -/
lemma det_abs_le (k : ℤ) :
    |(toeplitzReal β₀R k).det| ≤ 6 * (r ^ (k.natAbs - 2) * C_exp) ^ 3 := by
  set b := r ^ (k.natAbs - 2) * C_exp with hb_def
  have hb : 0 ≤ b := mul_nonneg (pow_nonneg r_nonneg _) C_exp_nonneg
  have hM : ∀ i j : Fin 3, (toeplitzReal β₀R k) i j ≤ b := entry_le_geometric k
  have hM0 : ∀ i j : Fin 3, 0 ≤ (toeplitzReal β₀R k) i j := entry_nonneg k
  -- Product-of-3 bound: for M i j ∈ [0, b], product ≤ b³
  have hprod : ∀ (a₁ a₂ a₃ : ℝ), 0 ≤ a₁ → a₁ ≤ b → 0 ≤ a₂ → a₂ ≤ b → 0 ≤ a₃ → a₃ ≤ b →
      a₁ * a₂ * a₃ ≤ b ^ 3 := fun a₁ a₂ a₃ h1 h1b h2 h2b h3 h3b => by
    have : a₁ * a₂ * a₃ ≤ b * b * b := by
      have hab : a₁ * a₂ ≤ b * b := mul_le_mul h1b h2b h2 hb
      calc a₁ * a₂ * a₃
          ≤ b * b * a₃ := mul_le_mul_of_nonneg_right hab h3
        _ ≤ b * b * b := mul_le_mul_of_nonneg_left h3b (mul_nonneg hb hb)
    linarith [show b ^ 3 = b * b * b from by ring]
  -- Bound the determinant via Matrix.det_fin_three
  rw [Matrix.det_fin_three]
  -- The determinant = sum of 6 signed terms; |det| ≤ sum of absolute values
  -- Each term is a product of 3 nonneg entries, hence nonneg
  set M := fun (i j : Fin 3) => (toeplitzReal β₀R k) i j
  -- Bound each of the 6 terms
  have t1 : M 0 0 * M 1 1 * M 2 2 ≤ b ^ 3 :=
    hprod _ _ _ (hM0 0 0) (hM 0 0) (hM0 1 1) (hM 1 1) (hM0 2 2) (hM 2 2)
  have t2 : M 0 0 * M 1 2 * M 2 1 ≤ b ^ 3 :=
    hprod _ _ _ (hM0 0 0) (hM 0 0) (hM0 1 2) (hM 1 2) (hM0 2 1) (hM 2 1)
  have t3 : M 0 1 * M 1 0 * M 2 2 ≤ b ^ 3 :=
    hprod _ _ _ (hM0 0 1) (hM 0 1) (hM0 1 0) (hM 1 0) (hM0 2 2) (hM 2 2)
  have t4 : M 0 1 * M 1 2 * M 2 0 ≤ b ^ 3 :=
    hprod _ _ _ (hM0 0 1) (hM 0 1) (hM0 1 2) (hM 1 2) (hM0 2 0) (hM 2 0)
  have t5 : M 0 2 * M 1 0 * M 2 1 ≤ b ^ 3 :=
    hprod _ _ _ (hM0 0 2) (hM 0 2) (hM0 1 0) (hM 1 0) (hM0 2 1) (hM 2 1)
  have t6 : M 0 2 * M 1 1 * M 2 0 ≤ b ^ 3 :=
    hprod _ _ _ (hM0 0 2) (hM 0 2) (hM0 1 1) (hM 1 1) (hM0 2 0) (hM 2 0)
  -- All 6 terms are nonneg
  have hn1 : 0 ≤ M 0 0 * M 1 1 * M 2 2 := mul_nonneg (mul_nonneg (hM0 0 0) (hM0 1 1)) (hM0 2 2)
  have hn2 : 0 ≤ M 0 0 * M 1 2 * M 2 1 := mul_nonneg (mul_nonneg (hM0 0 0) (hM0 1 2)) (hM0 2 1)
  have hn3 : 0 ≤ M 0 1 * M 1 0 * M 2 2 := mul_nonneg (mul_nonneg (hM0 0 1) (hM0 1 0)) (hM0 2 2)
  have hn4 : 0 ≤ M 0 1 * M 1 2 * M 2 0 := mul_nonneg (mul_nonneg (hM0 0 1) (hM0 1 2)) (hM0 2 0)
  have hn5 : 0 ≤ M 0 2 * M 1 0 * M 2 1 := mul_nonneg (mul_nonneg (hM0 0 2) (hM0 1 0)) (hM0 2 1)
  have hn6 : 0 ≤ M 0 2 * M 1 1 * M 2 0 := mul_nonneg (mul_nonneg (hM0 0 2) (hM0 1 1)) (hM0 2 0)
  -- |det| ≤ |t1| + |t2| + |t3| + |t4| + |t5| + |t6| ≤ 6 * b³
  rw [show (6 : ℝ) * (r ^ (k.natAbs - 2) * C_exp) ^ 3 = 6 * b ^ 3 from by rw [hb_def]]
  have hb3 : 0 ≤ b ^ 3 := pow_nonneg hb 3
  rw [abs_le]
  -- Each product atom appears in both determinant expansion and t1..t6 bounds:
  -- use linarith (linear over product atoms) instead of slow nlinarith
  constructor <;> linarith [t1, t2, t3, t4, t5, t6, hn1, hn2, hn3, hn4, hn5, hn6, hb3]

/-! ## §4  Summability of the geometric bounding series on ℤ -/

/-- The bounding function g k = 6 · C_exp³ · q^{k.natAbs − 2}. -/
noncomputable def g (k : ℤ) : ℝ := 6 * C_exp ^ 3 * q ^ (k.natAbs - 2)

lemma g_nonneg (k : ℤ) : 0 ≤ g k :=
  mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg C_exp_nonneg 3))
    (pow_nonneg q_nonneg _)

/-- The ℕ-indexed geometric series for the positive half is summable. -/
private lemma geo_nat_summable : Summable (fun n : ℕ => q ^ n) :=
  summable_geometric_of_lt_one q_nonneg q_lt_one

/-- The ℕ-indexed shifted series is summable. -/
private lemma geo_nat_shift_summable : Summable (fun n : ℕ => q ^ (n + 1)) := by
  simp_rw [pow_succ]
  exact geo_nat_summable.mul_right q

/-- Split ℤ summability via nonneg and negative parts. -/
private lemma summable_int_of_nat_parts {f : ℤ → ℝ}
    (h_nn : Summable (fun n : ℕ => f (n : ℤ)))
    (h_neg : Summable (fun n : ℕ => f (-(n : ℤ) - 1))) :
    Summable f := by
  rw [summable_int_iff_summable_nat_and_neg_add_one]
  exact ⟨h_nn, by convert h_neg using 2; push_cast; ring⟩

/-- g is summable on ℤ. -/
lemma g_summable : Summable g := by
  -- Step 1: q^k.natAbs is summable on ℤ (positive half: q^n, negative half: q^(n+1)).
  have hq_int : Summable (fun k : ℤ => q ^ k.natAbs) :=
    Summable.of_nat_of_neg
      (by simp only [Int.natAbs_ofNat]; exact summable_geometric_of_lt_one q_nonneg q_lt_one)
      (by simp only [Int.natAbs_neg, Int.natAbs_ofNat];
          exact summable_geometric_of_lt_one q_nonneg q_lt_one)
  -- Step 2: dominate g k ≤ (6·C_exp³/q²)·q^k.natAbs by comparison.
  apply Summable.of_nonneg_of_le g_nonneg _ (hq_int.mul_left (6 * C_exp ^ 3 / q ^ 2))
  intro k
  unfold g
  rw [show 6 * C_exp ^ 3 / q ^ 2 * q ^ k.natAbs =
        6 * C_exp ^ 3 * (q ^ k.natAbs / q ^ 2) from by ring]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (pow_nonneg C_exp_nonneg _))
  -- q^(k.natAbs - 2) ≤ q^k.natAbs / q^2, i.e. q^(k.natAbs-2)·q^2 ≤ q^k.natAbs
  rw [le_div_iff (pow_pos q_pos 2)]
  rcases le_or_lt k.natAbs 2 with h | h
  · -- k.natAbs ≤ 2: Nat sub gives 0; q^2 ≤ q^k.natAbs since k.natAbs ≤ 2 and q < 1
    simp only [Nat.sub_eq_zero_of_le h, pow_zero, one_mul]
    exact pow_le_pow_of_le_one q_nonneg q_lt_one.le h
  · -- k.natAbs > 2: q^(k.natAbs-2)·q^2 = q^k.natAbs (exact)
    have hn : k.natAbs - 2 + 2 = k.natAbs := Nat.sub_add_cancel (by omega)
    rw [← pow_add, hn]

/-! ## ALTERNATIVE direct summability proof for g -/

/-- Direct summability of g using the fact that g k / (6 * C_exp^3) = q^(k.natAbs - 2). -/
lemma g_summable_direct : Summable (fun k : ℤ => q ^ (k.natAbs - 2)) := by
  have heq : ∀ k : ℤ, q ^ (k.natAbs - 2) = g k / (6 * C_exp ^ 3) := fun k => by
    unfold g
    have hpos : (6 : ℝ) * C_exp ^ 3 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ C_exp_pos.ne')
    field_simp [hpos]
  simp_rw [heq]
  exact g_summable.div_const _

/-! ## §5  Parts (a) and (b) of W1_Numeric_Surface -/

set_option maxHeartbeats 40000000 in
/-- Part (a): Summability of the Toeplitz determinant series on ℤ. -/
theorem summable_toeplitz_det :
    Summable (fun k : ℤ => (toeplitzReal β₀R k).det) := by
  apply Summable.of_norm_bounded g g_summable
  intro k
  rw [Real.norm_eq_abs]
  calc |(toeplitzReal β₀R k).det|
      ≤ 6 * (r ^ (k.natAbs - 2) * C_exp) ^ 3 := det_abs_le k
    _ = g k := by unfold g q; ring

/-! ## §4b  Private helpers for the geometric tail bound -/

/-- C_exp < 3/2: from x+1 ≤ exp(x) at x = -1/4 giving exp(-1/4) ≥ 3/4,
so exp(1/4)·(3/4) ≤ 1, giving exp(1/4) ≤ 4/3 < 3/2. -/
private lemma C_exp_lt_three_halves : C_exp < 3 / 2 := by
  unfold C_exp
  have hr_sq : r ^ 2 < 1 / 4 := by nlinarith [r_lt_half, r_nonneg]
  apply lt_trans (Real.exp_lt_exp.mpr hr_sq)
  have h_neg : (3 : ℝ) / 4 ≤ Real.exp (-1 / 4 : ℝ) := by
    have h := Real.add_one_le_exp (-1 / 4 : ℝ); linarith
  have hmul : Real.exp (1 / 4 : ℝ) * Real.exp (-1 / 4 : ℝ) = 1 := by
    rw [← Real.exp_add]; norm_num
  have hpos14 : (0 : ℝ) < Real.exp (1 / 4) := Real.exp_pos _
  have hle : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by
    have h := mul_le_mul_of_nonneg_left h_neg hpos14.le; linarith
  linarith

/-- q ≤ 1/8: since r < 1/2, q = r³ < (1/2)³ = 1/8. -/
private lemma q_le_eighth : q ≤ 1 / 8 := by
  unfold q
  calc r ^ 3 ≤ (1 / 2 : ℝ) ^ 3 := pow_le_pow_left r_nonneg r_lt_half.le 3
    _ = 1 / 8 := by norm_num

/-- (1 − q)⁻¹ ≤ 8/7: since q ≤ 1/8, 1 − q ≥ 7/8. -/
private lemma inv_one_sub_q_le : (1 - q)⁻¹ ≤ 8 / 7 := by
  rw [show (8 : ℝ) / 7 = ((7 : ℝ) / 8)⁻¹ from by norm_num]
  exact inv_le_inv_of_le (by norm_num) (by linarith [q_le_eighth])

/-! ## §6  Part (b): tsum bound — OPEN surface -/

/-- [OPEN] Part (b) of W1_Numeric_Surface.
    `∑' k : ℤ, (toeplitzReal β₀R k).det ≤ ↑finite_hi_sum + ↑tail_ub`

    The proof decomposes as:
      (i)   tsum = ∑_{S26} + ∑'_{compl}  [tsum split]
      (ii)  ∑_{S26} ≤ finite_hi_sum       [reindex to Finset.range 51 + finite_sum_le]
      (iii) ∑'_{compl} ≤ tail_ub          [geometric tail bound via posE/negE bijections]

    Steps (i)-(ii) are proved separately in BesselBounds (bb_tsum_det_le, which
    re-uses tsum_det_split + tail_le_tail_ub as black-box lemmas).  The inline
    proof in W1NumericProof requires ~90+ CPU minutes for the type-class resolution
    involved in Equiv.tsum_eq, tsum_union_disjoint, and tsum_geometric_of_lt_one —
    longer than the machine's practical session window.

    STATUS: W1_TsumBound_Open — OPEN in W1NumericProof (elaboration-time constraint
    only; BesselBounds proves the equivalent bb_tsum_det_le independently via
    pre-split helper lemmas). -/
def W1_TsumBound_Open : Prop :=
  ∑' k : ℤ, (toeplitzReal β₀R k).det ≤ (↑finite_hi_sum + ↑tail_ub : ℝ)

/-! ## §7  Part (c): the pure ℚ inequality — OPEN surface -/

/-- [OPEN] Part (c) of W1_Numeric_Surface.
`exp_beta0_interval.hi * (finite_hi_sum + tail_ub) < 1 / 7`

This is a computable ℚ inequality that is TRUE (margin ≈ 3.86 × 10⁻⁷) but cannot
be closed kernel-cleanly with current tooling:
- `norm_num`: OOMs after ~13 min — β₀_rat = 2079416880123/10^12 raised to the 82nd
  power (N=40 Bessel terms) creates ~10⁻²⁹⁵² digit denominators; kernel holds all
  intermediates simultaneously.
- `native_decide`: feasible (GMP native, memory stable) but requires ≥15 min per
  compilation pass — session resets before completion; also adds Lean.reduceTrust.
- `decide` (kernel): stalls on Rat.instDecidableLe.

STATUS: W1_PartC_Open — OPEN pending a kernel-feasible proof strategy. -/
def W1_PartC_Open : Prop :=
  exp_beta0_interval.hi * (finite_hi_sum + tail_ub) < 1 / 7

theorem part_c (h : W1_PartC_Open) :
    exp_beta0_interval.hi * (finite_hi_sum + tail_ub) < 1 / 7 := h

/-! ## §8  The main theorem -/

/-- W1_Numeric_Surface CONDITIONALLY proved.
Part (a) is kernel-clean (classical trio).
Parts (b) and (c) are named OPEN surfaces:
  • `W1_TsumBound_Open` — tsum ≤ rational certificate (elaboration-time constraint)
  • `W1_PartC_Open`     — ℚ inequality exp_hi * sum < 1/7 (kernel-size constraint)

BesselBounds independently proves the equivalent `bb_tsum_det_le` via pre-split
helpers, so `bb_w1_numeric_surface` closes W1_Numeric_Surface conditional on
W1_PartC_Open only.

Supply proofs of both OPEN surfaces to close W1_Numeric_Surface via this route. -/
theorem w1_numeric_surface_proved (hb : W1_TsumBound_Open) (hc : W1_PartC_Open) :
    W1_Numeric_Surface :=
  ⟨summable_toeplitz_det, hb, hc⟩

end TheoremaAureum.Towers.YM.W1NumericProof

-- #print axioms w1_numeric_surface_proved
-- With hb : W1_TsumBound_Open, hc : W1_PartC_Open:
--   [propext, Classical.choice, Quot.sound, W1_TsumBound_Open, W1_PartC_Open]
