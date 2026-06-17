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
-- PART (b): named open surface TsumDetLe_Surface — closed by BesselBounds.bb_tsum_det_le.
--   Two gaps (tsum split + geometric tail) discharged in BesselBounds.lean (sorry: 0).
--
-- PART (c): pure ℚ — proved by `decide` (kernel reduction of computable ℚ).
/-
W1NumericProof — Infrastructure for W1_Numeric_Surface.
Part (b) sorry-holes converted to named open surface TsumDetLe_Surface (2026-06-17).
Canonical sorry-free proof: BesselBounds.bb_w1_numeric_surface.
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

lemma r_pos : 0 < r := by unfold r β₀R; positivity
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
  · exact pow_nonneg (div_nonneg (by positivity) two_pos.le) _
  · positivity

/-- Entry ≤ r^{|i−j−k|} · C_exp, by besselI_series_le_exp_bound. -/
lemma entry_le_pow_mul (k : ℤ) (i j : Fin 3) :
    (toeplitzReal β₀R k) i j ≤ r ^ ((i : ℤ) - j - k).natAbs * C_exp := by
  simp only [toeplitzReal, Matrix.of_apply]
  have hx : 0 ≤ β₀R / 3 := by positivity
  apply le_trans (besselI_series_le_exp_bound _ _ hx)
  have hr : β₀R / 3 / 2 = r := by unfold r; ring
  simp only [hr, C_exp]

/-- Reverse triangle: index |i−j−k| ≥ k.natAbs − 2 (natural subtraction). -/
lemma index_lower_bound (k : ℤ) (i j : Fin 3) :
    k.natAbs - 2 ≤ ((i : ℤ) - j - k).natAbs := by
  have hij : ((i : ℤ) - j).natAbs ≤ 2 := by
    fin_cases i <;> fin_cases j <;> simp [Int.natAbs]
  have heq : (k : ℤ) = -((i : ℤ) - j - k) + ((i : ℤ) - j) := by ring
  have hkey : k.natAbs ≤ ((i : ℤ) - j - k).natAbs + ((i : ℤ) - j).natAbs := by
    calc k.natAbs
        = (-((i : ℤ) - j - k) + ((i : ℤ) - j)).natAbs := by conv_lhs => rw [heq]
      _ ≤ (-(i - j - k)).natAbs + (i - j).natAbs := Int.natAbs_add_le _ _
      _ = (i - j - k).natAbs + (i - j).natAbs := by rw [Int.natAbs_neg]
  omega

/-- For all k : ℤ, every entry ≤ r^{k.natAbs − 2} · C_exp. -/
lemma entry_le_geometric (k : ℤ) (i j : Fin 3) :
    (toeplitzReal β₀R k) i j ≤ r ^ (k.natAbs - 2) * C_exp := by
  apply le_trans (entry_le_pow_mul k i j)
  gcongr
  · exact r_nonneg
  · exact r_lt_one.le
  · exact index_lower_bound k i j

/-! ## §3  Determinant absolute-value bound -/

/-- |det(toeplitzReal β₀ k)| ≤ 6 · (r^{k.natAbs−2} · C_exp)³ for all k. -/
lemma det_abs_le (k : ℤ) :
    |(toeplitzReal β₀R k).det| ≤ 6 * (r ^ (k.natAbs - 2) * C_exp) ^ 3 := by
  set b := r ^ (k.natAbs - 2) * C_exp with hb_def
  have hb : 0 ≤ b := mul_nonneg (pow_nonneg r_nonneg _) C_exp_nonneg
  have hM : ∀ i j : Fin 3, (toeplitzReal β₀R k) i j ≤ b := entry_le_geometric k
  have hM0 : ∀ i j : Fin 3, 0 ≤ (toeplitzReal β₀R k) i j := entry_nonneg k
  have hprod : ∀ (a₁ a₂ a₃ : ℝ), 0 ≤ a₁ → a₁ ≤ b → 0 ≤ a₂ → a₂ ≤ b → 0 ≤ a₃ → a₃ ≤ b →
      a₁ * a₂ * a₃ ≤ b ^ 3 := fun a₁ a₂ a₃ h1 h1b h2 h2b h3 h3b => by
    have : a₁ * a₂ * a₃ ≤ b * b * b := by
      calc a₁ * a₂ * a₃
          ≤ b * b * a₃ := by nlinarith [mul_nonneg h1 h2]
        _ ≤ b * b * b := by nlinarith [mul_nonneg hb hb]
    linarith [show b ^ 3 = b * b * b from by ring]
  rw [Matrix.det_fin_three]
  set M := fun (i j : Fin 3) => (toeplitzReal β₀R k) i j
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
  have hn1 : 0 ≤ M 0 0 * M 1 1 * M 2 2 := mul_nonneg (mul_nonneg (hM0 0 0) (hM0 1 1)) (hM0 2 2)
  have hn2 : 0 ≤ M 0 0 * M 1 2 * M 2 1 := mul_nonneg (mul_nonneg (hM0 0 0) (hM0 1 2)) (hM0 2 1)
  have hn3 : 0 ≤ M 0 1 * M 1 0 * M 2 2 := mul_nonneg (mul_nonneg (hM0 0 1) (hM0 1 0)) (hM0 2 2)
  have hn4 : 0 ≤ M 0 1 * M 1 2 * M 2 0 := mul_nonneg (mul_nonneg (hM0 0 1) (hM0 1 2)) (hM0 2 0)
  have hn5 : 0 ≤ M 0 2 * M 1 0 * M 2 1 := mul_nonneg (mul_nonneg (hM0 0 2) (hM0 1 0)) (hM0 2 1)
  have hn6 : 0 ≤ M 0 2 * M 1 1 * M 2 0 := mul_nonneg (mul_nonneg (hM0 0 2) (hM0 1 1)) (hM0 2 0)
  rw [show (6 : ℝ) * (r ^ (k.natAbs - 2) * C_exp) ^ 3 = 6 * b ^ 3 from by rw [hb_def]]
  have := abs_sub_abs_le_abs_sub
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.head_fin_const]
  rw [abs_le]
  constructor <;> linarith

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
  exact geo_nat_summable.mul_left q

/-- Split ℤ summability via nonneg and negative parts. -/
private lemma summable_int_of_nat_parts {f : ℤ → ℝ}
    (h_nn : Summable (fun n : ℕ => f (n : ℤ)))
    (h_neg : Summable (fun n : ℕ => f (-(n : ℤ) - 1))) :
    Summable f := by
  exact summable_int_of_summable_nat h_nn h_neg

/-- g is summable on ℤ. -/
lemma g_summable : Summable g := by
  have hq_int : Summable (fun k : ℤ => q ^ k.natAbs) :=
    summable_int_of_summable_nat
      (by simp only [Int.natAbs_ofNat]; exact summable_geometric_of_lt_one q_nonneg q_lt_one)
      (by simp only [Int.natAbs_negSucc]
          simp_rw [pow_succ]
          exact (summable_geometric_of_lt_one q_nonneg q_lt_one).mul_left q)
  apply Summable.of_nonneg_of_le g_nonneg _ (hq_int.mul_left (6 * C_exp ^ 3 / q ^ 2))
  intro k
  unfold g
  rw [show 6 * C_exp ^ 3 / q ^ 2 * q ^ k.natAbs =
        6 * C_exp ^ 3 * (q ^ k.natAbs / q ^ 2) from by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [le_div_iff (pow_pos q_pos 2)]
  rcases le_or_lt k.natAbs 2 with h | h
  · simp only [Nat.sub_eq_zero_of_le h, pow_zero, one_mul]
    exact pow_le_pow_of_le_one q_nonneg q_lt_one.le h
  · have hn : k.natAbs - 2 + 2 = k.natAbs := Nat.sub_add_cancel (by omega)
    rw [← pow_add, hn]

/-! ## §5  Part (a) of W1_Numeric_Surface -/

/-- Part (a): Summability of the Toeplitz determinant series on ℤ. -/
theorem summable_toeplitz_det :
    Summable (fun k : ℤ => (toeplitzReal β₀R k).det) := by
  apply Summable.of_norm_bounded g g_summable
  intro k
  apply le_trans (det_abs_le k)
  unfold g q
  ring_nf

/-! ## §6  Part (b): named open surface — closed by BesselBounds.lean -/

/-- **Open surface** (closed by `BesselBounds.bb_tsum_det_le`, sorry-free, 2026-06-17).
The ℤ-tsum of Toeplitz determinants is bounded above by `finite_hi_sum + tail_ub`.
Two gaps discharged in BesselBounds:
  (1) tsum split → `Finset.sum_add_tsum_compl`  (§11 of BesselBounds)
  (2) geometric tail ≤ 1/10^20 → ℕ-bijections + `tsum_geometric_of_lt_one`  (§9–§10).
NOT an axiom — a named Prop def; `BesselBounds.lean` is the canonical proof. -/
def TsumDetLe_Surface : Prop :=
  ∑' k : ℤ, (toeplitzReal β₀R k).det ≤ (↑finite_hi_sum + ↑tail_ub : ℝ)

/-! ## §7  Part (c): the pure ℚ inequality -/

/-- Part (c): exp_hi · (finite_hi_sum + tail_ub) < 1/7. Pure ℚ, kernel-decidable. -/
theorem part_c : exp_beta0_interval.hi * (finite_hi_sum + tail_ub) < 1 / 7 := by
  decide

/-! ## §8  Honest conditional combinator -/

/-- **W1_Numeric_Surface** from the open surface + parts (a) and (c).
Canonical sorry-free proof: `BesselBounds.bb_w1_numeric_surface`
  = ⟨summable_toeplitz_det, bb_tsum_det_le, bb_part_c⟩.
Classical trio only when called with BesselBounds.TsumDetLe_Surface proved. -/
theorem w1_numeric_surface_of_tsum (h : TsumDetLe_Surface) : W1_Numeric_Surface :=
  ⟨summable_toeplitz_det, h, part_c⟩

end TheoremaAureum.Towers.YM.W1NumericProof

-- #print axioms w1_numeric_surface_of_tsum
-- Expected (with BesselBounds): [propext, Classical.choice, Quot.sound]
