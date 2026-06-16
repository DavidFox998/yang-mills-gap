-- Axiom status: Classical trio only. 0 gaps. 0 new axioms.
-- PROVES: w1_weyl_series (11/5 : ℝ) < 1/7
-- CLOSES: W1_one_seventh_Surface in KP_Closure.lean (β₇ = 11/5 = 2.20).
-- Mirror of KP_W1_Proof.lean with tighter bounds (smaller β, looser target).
--
-- Numeric summary (β₇ = 11/5 = 2.20):
--   r₇ = β₇/6 = 11/30 ≈ 0.3667  (< 1/2)
--   q₇ = r₇^3 = 1331/27000 ≈ 0.0493  (< 1/8)
--   C_exp₇ = exp(r₇^2) < exp(1/4) < 3/2
--   exp(-β₇) ≈ 0.11080
--   Window: Icc(-5,5), 11 terms; complement: |k| ≥ 6, k.natAbs-2 ≥ 4
--   Tail: 2·6·(3/2)³·(1/8)⁴·(8/7) = 81/7168 ≤ 3/200 = tail_7_ub
--   Part(c): P_28(β₇)·(finite_7_hi_sum + 3/200) < 1/7  [decide]
--   Actual: P_28·(F+T) ≈ 0.11080 × 1.178 ≈ 0.1304 < 1/7 ≈ 0.1429. Margin ≈ 0.0124.

import Towers.YM.BesselBounds

namespace TheoremaAureum.Towers.YM.W1SeventhProof

open Real BigOperators Finset
open TheoremaAureum.Towers.YM.WeylToeplitzBound
open TheoremaAureum.Towers.YM.IntervalArith
open TheoremaAureum.Towers.YM.BesselSeries RatInterval

/-! ## §0  β₇ constants -/

/-- β₇ = 11/5 = 2.20 exactly. -/
def β₇_rat : ℚ := 11 / 5

private local notation "βR₇" => (β₇_rat : ℝ)
private abbrev S6k7 : Finset ℤ := Finset.Icc (-5) 5

/-! ## §1  Decay constants -/

noncomputable def r₇ : ℝ := βR₇ / 6
noncomputable def q₇ : ℝ := r₇ ^ 3
noncomputable def C_exp₇ : ℝ := Real.exp (r₇ ^ 2)

private lemma r₇_pos : 0 < r₇ := by norm_num [r₇, β₇_rat]
private lemma r₇_nonneg : 0 ≤ r₇ := r₇_pos.le
-- r₇ = 11/30 < 1/2
private lemma r₇_lt_half : r₇ < 1 / 2 := by unfold r₇; norm_num [β₇_rat]
private lemma r₇_lt_one : r₇ < 1 := lt_trans r₇_lt_half (by norm_num)
private lemma q₇_pos : 0 < q₇ := pow_pos r₇_pos 3
private lemma q₇_nonneg : 0 ≤ q₇ := q₇_pos.le
private lemma q₇_lt_one : q₇ < 1 :=
  pow_lt_one r₇_nonneg r₇_lt_one (by norm_num)
-- q₇ = r₇^3 < (1/2)^3 = 1/8
private lemma q₇_lt_eighth : q₇ < 1 / 8 := by
  unfold q₇
  calc r₇ ^ 3 < (1 / 2 : ℝ) ^ 3 :=
        pow_lt_pow_left r₇_nonneg r₇_lt_half 3
    _ = 1 / 8 := by norm_num
private lemma C_exp₇_pos : 0 < C_exp₇ := Real.exp_pos _
private lemma C_exp₇_nonneg : 0 ≤ C_exp₇ := C_exp₇_pos.le
-- C_exp₇ = exp(r₇^2) < exp(1/4) < 3/2
private lemma C_exp₇_lt_three_halves : C_exp₇ < 3 / 2 := by
  unfold C_exp₇
  have hr_sq : r₇ ^ 2 < 1 / 4 := by nlinarith [r₇_lt_half, r₇_nonneg]
  have h1 : Real.exp (r₇ ^ 2) < Real.exp (1 / 4) := Real.exp_lt_exp.mpr hr_sq
  have h4 : Real.exp (1 / 4 : ℝ) ^ 4 = Real.exp 1 := by rw [← Real.exp_natMul]; norm_num
  have hd9 : Real.exp 1 < 2.7183 := by linarith [Real.exp_one_lt_d9]
  have hpos : (0 : ℝ) < Real.exp (1 / 4 : ℝ) := Real.exp_pos _
  have hlt4 : Real.exp (1 / 4 : ℝ) ^ 4 < (3 / 2 : ℝ) ^ 4 := by
    linarith [show (3 / 2 : ℝ) ^ 4 = 81 / 16 from by norm_num]
  exact lt_trans h1 (lt_of_pow_lt_pow_left 4 (by norm_num) hlt4)
-- (1 - q₇)^{-1} ≤ 8/7  [q₇ < 1/8 → 1-q₇ > 7/8]
private lemma inv_one_sub_q₇_le : (1 - q₇)⁻¹ ≤ 8 / 7 := by
  rw [show (8 : ℝ) / 7 = ((7 : ℝ) / 8)⁻¹ from by norm_num]
  apply inv_le_inv_of_le (by norm_num : (0 : ℝ) < 7 / 8)
  linarith [q₇_lt_eighth]

/-! ## §2  Entry bounds -/

private lemma entry₇_nonneg (k : ℤ) (i j : Fin 3) :
    0 ≤ (toeplitzReal βR₇ k) i j := by
  simp only [toeplitzReal, Matrix.of_apply]
  apply tsum_nonneg; intro n
  exact div_nonneg (pow_nonneg (div_nonneg (by norm_num [β₇_rat]) two_pos.le) _) (by positivity)

private lemma entry₇_le_pow_mul (k : ℤ) (i j : Fin 3) :
    (toeplitzReal βR₇ k) i j ≤ r₇ ^ ((i : ℤ) - j - k).natAbs * C_exp₇ := by
  simp only [toeplitzReal, Matrix.of_apply]
  apply le_trans (besselI_series_le_exp_bound _ _ (by norm_num [β₇_rat]))
  have hr : βR₇ / 3 / 2 = r₇ := by unfold r₇; ring
  simp only [hr, C_exp₇]
  exact le_refl _

private lemma index₇_lower (k : ℤ) (i j : Fin 3) :
    k.natAbs - 2 ≤ ((i : ℤ) - j - k).natAbs := by
  have hij : ((i : ℤ) - j).natAbs ≤ 2 := by
    fin_cases i <;> fin_cases j <;> decide
  have heq : (k : ℤ) = -((i : ℤ) - j - k) + ((i : ℤ) - j) := by ring
  calc k.natAbs
      = (-((i : ℤ) - j - k) + ((i : ℤ) - j)).natAbs := by conv_lhs => rw [heq]
    _ ≤ (-((i : ℤ) - j - k)).natAbs + ((i : ℤ) - j).natAbs := Int.natAbs_add_le _ _
    _ = ((i : ℤ) - j - k).natAbs + ((i : ℤ) - j).natAbs := by rw [Int.natAbs_neg]
    _ ≤ ((i : ℤ) - j - k).natAbs + 2 := Nat.add_le_add_left hij _
  omega

private lemma entry₇_le_geometric (k : ℤ) (i j : Fin 3) :
    (toeplitzReal βR₇ k) i j ≤ r₇ ^ (k.natAbs - 2) * C_exp₇ :=
  le_trans (entry₇_le_pow_mul k i j)
    (by gcongr; exact r₇_lt_one.le; exact index₇_lower k i j)

/-! ## §3  Det absolute-value bound -/

noncomputable def g₇ (k : ℤ) : ℝ := 6 * C_exp₇ ^ 3 * q₇ ^ (k.natAbs - 2)

private lemma g₇_nonneg (k : ℤ) : 0 ≤ g₇ k :=
  mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg C_exp₇_nonneg 3)) (pow_nonneg q₇_nonneg _)

private lemma det_abs₇_le (k : ℤ) : |(toeplitzReal βR₇ k).det| ≤ g₇ k := by
  set b := r₇ ^ (k.natAbs - 2) * C_exp₇ with hb_def
  have hb : 0 ≤ b := mul_nonneg (pow_nonneg r₇_nonneg _) C_exp₇_nonneg
  have hM : ∀ i j : Fin 3, (toeplitzReal βR₇ k) i j ≤ b := entry₇_le_geometric k
  have hM0 : ∀ i j : Fin 3, 0 ≤ (toeplitzReal βR₇ k) i j := entry₇_nonneg k
  have hprod : ∀ a₁ a₂ a₃ : ℝ,
      0 ≤ a₁ → a₁ ≤ b → 0 ≤ a₂ → a₂ ≤ b → 0 ≤ a₃ → a₃ ≤ b → a₁ * a₂ * a₃ ≤ b ^ 3 :=
    fun a₁ a₂ a₃ h1 h1b h2 h2b h3 h3b => by
      nlinarith [mul_nonneg h1 h2, show b ^ 3 = b * b * b from by ring]
  have hgb : g₇ k = 6 * b ^ 3 := by
    unfold g₇ q₇ b
    rw [mul_pow, ← pow_mul, show (k.natAbs - 2) * 3 = 3 * (k.natAbs - 2) from mul_comm _ _,
        pow_mul]
    ring
  rw [Matrix.det_fin_three, hgb, abs_le]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]
  have t1 := hprod _ _ _ (hM0 0 0) (hM 0 0) (hM0 1 1) (hM 1 1) (hM0 2 2) (hM 2 2)
  have t2 := hprod _ _ _ (hM0 0 0) (hM 0 0) (hM0 1 2) (hM 1 2) (hM0 2 1) (hM 2 1)
  have t3 := hprod _ _ _ (hM0 0 1) (hM 0 1) (hM0 1 0) (hM 1 0) (hM0 2 2) (hM 2 2)
  have t4 := hprod _ _ _ (hM0 0 1) (hM 0 1) (hM0 1 2) (hM 1 2) (hM0 2 0) (hM 2 0)
  have t5 := hprod _ _ _ (hM0 0 2) (hM 0 2) (hM0 1 0) (hM 1 0) (hM0 2 1) (hM 2 1)
  have t6 := hprod _ _ _ (hM0 0 2) (hM 0 2) (hM0 1 1) (hM 1 1) (hM0 2 0) (hM 2 0)
  constructor <;> linarith

/-! ## §4  Summability -/

private lemma seven_natAbs_summable : Summable (fun k : ℤ => q₇ ^ k.natAbs) := by
  apply (Int.summable_iff).mpr
  exact ⟨by simp_rw [Function.comp, Int.natAbs_ofNat]
             exact summable_geometric_of_lt_one q₇_nonneg q₇_lt_one,
         by simp_rw [Int.natAbs_negSucc, pow_succ]
            exact (summable_geometric_of_lt_one q₇_nonneg q₇_lt_one).mul_left q₇⟩

lemma g₇_summable : Summable g₇ := by
  apply Summable.of_nonneg_of_le g₇_nonneg _
    (seven_natAbs_summable.mul_left (6 * C_exp₇ ^ 3 / q₇ ^ 2))
  intro k
  unfold g₇
  rw [show 6 * C_exp₇ ^ 3 / q₇ ^ 2 * q₇ ^ k.natAbs =
        6 * C_exp₇ ^ 3 * (q₇ ^ k.natAbs / q₇ ^ 2) from by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [le_div_iff (pow_pos q₇_pos 2)]
  rcases le_or_lt k.natAbs 2 with h | h
  · simp only [Nat.sub_eq_zero_of_le h, pow_zero, one_mul]
    exact pow_le_pow_of_le_one q₇_nonneg q₇_lt_one.le h
  · have hn : k.natAbs - 2 + 2 = k.natAbs := Nat.sub_add_cancel (by omega)
    rw [← pow_add, hn]

theorem summable_toeplitz_det₇ :
    Summable (fun k : ℤ => (toeplitzReal βR₇ k).det) := by
  apply Summable.of_norm_bounded g₇ g₇_summable
  intro k; rw [Real.norm_eq_abs]; exact det_abs₇_le k

/-! ## §5  Exp upper bound via Taylor-Lagrange (N=28, even) -/

private theorem seven_iterDeriv (n : ℕ) :
    ∀ t ∈ Set.Icc (0 : ℝ) βR₇,
      iteratedDerivWithin n (fun s => Real.exp (-s)) (Set.Icc 0 βR₇) t =
        (-1 : ℝ) ^ n * Real.exp (-t) := by
  have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) βR₇) :=
    uniqueDiffOn_Icc (by norm_num [β₇_rat])
  induction n with
  | zero => intro t _; simp [iteratedDerivWithin_zero]
  | succ n ih =>
    intro t ht
    rw [iteratedDerivWithin_succ (hu t ht),
        derivWithin_congr (fun y hy => ih y hy) (ih t ht)]
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-t)) t := by
      have := (Real.hasDerivAt_exp (-t)).comp t ((hasDerivAt_id t).neg); simpa using this
    rw [(h1.const_mul ((-1 : ℝ) ^ n)).hasDerivWithinAt.derivWithin (hu t ht), pow_succ]; ring

private theorem seven_taylorPoly_eq :
    taylorWithinEval (fun t : ℝ => Real.exp (-t)) 28 (Set.Icc 0 βR₇) 0 βR₇ =
      ((exp_neg_partial β₇_rat 28 : ℚ) : ℝ) := by
  rw [taylor_within_apply, exp_neg_partial, Rat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) βR₇ := ⟨le_refl _, by norm_num [β₇_rat]⟩
  rw [seven_iterDeriv k 0 h0]
  simp only [neg_zero, Real.exp_zero, mul_one, sub_zero, smul_eq_mul]
  push_cast; ring

theorem exp₇_upper : Real.exp (-βR₇) ≤ ((exp_neg_partial β₇_rat 28 : ℚ) : ℝ) := by
  have hpos : (0 : ℝ) < βR₇ := by norm_num [β₇_rat]
  have hcd : ContDiffOn ℝ 28 (fun t : ℝ => Real.exp (-t)) (Set.Icc 0 βR₇) := by fun_prop
  have hcd' : ContDiffOn ℝ (29 : ℕ∞) (fun t : ℝ => Real.exp (-t)) (Set.Icc 0 βR₇) := by fun_prop
  have hdiff : DifferentiableOn ℝ
      (iteratedDerivWithin 28 (fun t : ℝ => Real.exp (-t)) (Set.Icc 0 βR₇)) (Set.Ioo 0 βR₇) :=
    (hcd'.differentiableOn_iteratedDerivWithin (by norm_num : (28 : ℕ∞) < 29)
      (uniqueDiffOn_Icc hpos)).mono Set.Ioo_subset_Icc_self
  obtain ⟨x', hx'mem, hrem⟩ := taylor_mean_remainder_lagrange hpos hcd hdiff
  rw [seven_iterDeriv 29 x' (Set.Ioo_subset_Icc_self hx'mem), seven_taylorPoly_eq] at hrem
  have hQpos : (0 : ℝ) < Real.exp (-x') * (βR₇ ^ 29 / ((29 : ℝ).factorial)) :=
    mul_pos (Real.exp_pos _) (div_pos (pow_pos hpos 29) (by exact_mod_cast Nat.factorial_pos 29))
  nlinarith [show ((-1 : ℝ) ^ 29) = -1 from by norm_num]

/-! ## §6  Bessel enclosures for β₇/3 -/

def besselIn_seven_interval (n : ℕ) : RatInterval :=
  besselIn_interval n (ofRat (β₇_rat / 3)) 40

private lemma seven_q_pos : (0 : ℚ) < β₇_rat / 3 := by norm_num [β₇_rat]
private lemma seven_q_half_nn : (0 : ℚ) ≤ β₇_rat / 3 / 2 := by norm_num [β₇_rat]
private lemma seven_q_half_le1 : β₇_rat / 3 / 2 ≤ 1 := by norm_num [β₇_rat]
-- β₇/3/2 = 11/30; (11/30)²/(n+42) < 1 for all n≥0
private lemma seven_r1Q (n : ℕ) : (β₇_rat / 3 / 2) ^ 2 / ((n : ℚ) + 40 + 2) < 1 := by
  rw [div_lt_one (by positivity)]
  have : (β₇_rat / 3 / 2) ^ 2 < 42 := by norm_num [β₇_rat]
  push_cast; linarith [Nat.cast_nonneg (α := ℚ) n]

private lemma seven_err_nonneg (n : ℕ) : 0 ≤ besselIn_error n (β₇_rat / 3) 40 := by
  unfold besselIn_error
  apply div_nonneg
  · exact div_nonneg (pow_nonneg (div_nonneg seven_q_pos.le (by norm_num)) _) (by positivity)
  · linarith [seven_r1Q n]

private lemma seven_lo_eq (n : ℕ) :
    (besselIn_seven_interval n).lo = besselIn_partial n (β₇_rat / 3) 40 := by
  simp only [besselIn_seven_interval, besselIn_interval, ofRat]
  exact min_eq_left (le_add_of_nonneg_right (seven_err_nonneg n))

private lemma seven_hi_eq (n : ℕ) :
    (besselIn_seven_interval n).hi =
      besselIn_partial n (β₇_rat / 3) 40 + besselIn_error n (β₇_rat / 3) 40 := by
  simp only [besselIn_seven_interval, besselIn_interval, ofRat]
  exact max_eq_right (le_add_of_nonneg_right (seven_err_nonneg n))

-- Local copy of besseln_tail (private in KPW1Proof)
private theorem besseln_tail₇_local (n : ℕ) (y : ℝ) (N : ℕ) (hy : 0 ≤ y)
    (hr1 : (y / 2) ^ 2 / ((n : ℝ) + N + 2) < 1) :
    ∑' i : ℕ, (y / 2) ^ (n + 2 * (i + (N + 1)))
        / (((i + (N + 1)).factorial : ℝ) * ((n + (i + (N + 1))).factorial : ℝ))
      ≤ ((y / 2) ^ (n + 2 * (N + 1)) /
           (((N + 1).factorial : ℝ) * ((n + (N + 1)).factorial : ℝ)))
          / (1 - (y / 2) ^ 2 / ((n : ℝ) + N + 2)) := by
  have hr0 : 0 ≤ (y / 2) ^ 2 / ((n : ℝ) + N + 2) := by positivity
  have hT : Summable (fun k : ℕ =>
      (y / 2) ^ (n + 2 * k) / ((k.factorial : ℝ) * ((n + k).factorial : ℝ))) :=
    besselI_series_summable n y
  have htail_s : Summable (fun i : ℕ =>
      (y / 2) ^ (n + 2 * (i + (N + 1)))
        / (((i + (N + 1)).factorial : ℝ) * ((n + (i + (N + 1))).factorial : ℝ))) :=
    (summable_nat_add_iff (N + 1)).mpr hT
  have hgeom_s : Summable (fun i : ℕ =>
      ((y / 2) ^ (n + 2 * (N + 1)) /
           (((N + 1).factorial : ℝ) * ((n + (N + 1)).factorial : ℝ)))
        * ((y / 2) ^ 2 / ((n : ℝ) + N + 2)) ^ i) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hterm : ∀ i : ℕ,
      (y / 2) ^ (n + 2 * (i + (N + 1)))
          / (((i + (N + 1)).factorial : ℝ) * ((n + (i + (N + 1))).factorial : ℝ))
        ≤ ((y / 2) ^ (n + 2 * (N + 1)) /
              (((N + 1).factorial : ℝ) * ((n + (N + 1)).factorial : ℝ)))
            * ((y / 2) ^ 2 / ((n : ℝ) + N + 2)) ^ i := by
    intro i
    have h1 : (N + 1).factorial ≤ (i + (N + 1)).factorial :=
      Nat.factorial_le (by omega)
    have h2 : (n + (N + 1)).factorial * (n + N + 2) ^ i ≤ (n + (i + (N + 1))).factorial := by
      have h := Nat.factorial_mul_pow_le_factorial (m := n + (N + 1)) (n := i)
      rw [show n + (N + 1) + 1 = n + N + 2 from by omega,
          show n + (N + 1) + i = n + (i + (N + 1)) from by omega] at h
      exact h
    have hnat : (N + 1).factorial * (n + (N + 1)).factorial * (n + N + 2) ^ i
        ≤ (i + (N + 1)).factorial * (n + (i + (N + 1))).factorial :=
      calc (N + 1).factorial * (n + (N + 1)).factorial * (n + N + 2) ^ i
          = (N + 1).factorial * ((n + (N + 1)).factorial * (n + N + 2) ^ i) := by ring
        _ ≤ (i + (N + 1)).factorial * (n + (i + (N + 1))).factorial :=
              Nat.mul_le_mul h1 h2
    have hnatR :
        ((N + 1).factorial : ℝ) * ((n + (N + 1)).factorial : ℝ) * ((n : ℝ) + N + 2) ^ i
          ≤ ((i + (N + 1)).factorial : ℝ) * ((n + (i + (N + 1))).factorial : ℝ) :=
      by exact_mod_cast hnat
    rw [show n + 2 * (i + (N + 1)) = (n + 2 * (N + 1)) + 2 * i from by ring,
        pow_add, pow_mul, div_pow, mul_div_assoc]
    rw [show ((y / 2) ^ (n + 2 * (N + 1)) /
            (((N + 1).factorial : ℝ) * ((n + (N + 1)).factorial : ℝ)))
          * (((y / 2) ^ 2) ^ i / ((n : ℝ) + N + 2) ^ i)
        = ((y / 2) ^ (n + 2 * (N + 1)) * ((y / 2) ^ 2) ^ i) /
          ((((N + 1).factorial : ℝ) * ((n + (N + 1)).factorial : ℝ)) * ((n : ℝ) + N + 2) ^ i)
        from by ring]
    exact div_le_div_of_nonneg_left
      (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (sq_nonneg _) _))
      (by positivity) hnatR
  calc ∑' i : ℕ, (y / 2) ^ (n + 2 * (i + (N + 1)))
          / (((i + (N + 1)).factorial : ℝ) * ((n + (i + (N + 1))).factorial : ℝ))
      ≤ ∑' i : ℕ, ((y / 2) ^ (n + 2 * (N + 1)) /
              (((N + 1).factorial : ℝ) * ((n + (N + 1)).factorial : ℝ)))
            * ((y / 2) ^ 2 / ((n : ℝ) + N + 2)) ^ i :=
          tsum_le_tsum hterm htail_s hgeom_s
    _ = ((y / 2) ^ (n + 2 * (N + 1)) /
            (((N + 1).factorial : ℝ) * ((n + (N + 1)).factorial : ℝ)))
          * ∑' i : ℕ, ((y / 2) ^ 2 / ((n : ℝ) + N + 2)) ^ i := tsum_mul_left
    _ = ((y / 2) ^ (n + 2 * (N + 1)) /
            (((N + 1).factorial : ℝ) * ((n + (N + 1)).factorial : ℝ)))
          * (1 - (y / 2) ^ 2 / ((n : ℝ) + N + 2))⁻¹ := by
          rw [tsum_geometric_of_lt_one hr0 hr1]
    _ = _ := by ring

theorem besselIn_seven_contains (n : ℕ) :
    (besselIn_seven_interval n).contains (besselI_series n ((β₇_rat / 3 : ℚ) : ℝ)) := by
  set q : ℚ := β₇_rat / 3 with hq
  have hqpos : 0 < q := seven_q_pos
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hr1Q : (q / 2) ^ 2 / ((n : ℚ) + 40 + 2) < 1 := seven_r1Q n
  have hTsum : Summable (fun k : ℕ =>
      ((q : ℝ) / 2) ^ (n + 2 * k) / ((k.factorial : ℝ) * ((n + k).factorial : ℝ))) :=
    besselI_series_summable n (q : ℝ)
  have hg_nonneg : ∀ k : ℕ,
      0 ≤ ((q : ℝ) / 2) ^ (n + 2 * k) / ((k.factorial : ℝ) * ((n + k).factorial : ℝ)) :=
    fun k => div_nonneg (pow_nonneg (by linarith) _) (by positivity)
  have hcast_partial : ((besselIn_partial n q 40 : ℚ) : ℝ) =
      ∑ k ∈ Finset.range 41,
        ((q : ℝ) / 2) ^ (n + 2 * k) / ((k.factorial : ℝ) * ((n + k).factorial : ℝ)) := by
    unfold besselIn_partial; rw [Rat.cast_sum]
    exact Finset.sum_congr rfl fun k _ => by push_cast; ring
  have hcast_error : ((besselIn_error n q 40 : ℚ) : ℝ) =
      ((q : ℝ) / 2) ^ (n + 2 * (40 + 1))
          / (((40 + 1).factorial : ℝ) * ((n + (40 + 1)).factorial : ℝ))
        / (1 - ((q : ℝ) / 2) ^ 2 / ((n : ℝ) + (40 : ℝ) + 2)) := by
    unfold besselIn_error; push_cast; ring
  constructor
  · rw [seven_lo_eq, hcast_partial,
        show besselI_series n ((q : ℝ)) =
          ∑' k : ℕ, ((q : ℝ) / 2) ^ (n + 2 * k) /
            ((k.factorial : ℝ) * ((n + k).factorial : ℝ)) from rfl]
    exact sum_le_tsum _ (fun i _ => hg_nonneg i) hTsum
  · rw [seven_hi_eq]
    have hsplit : besselI_series n ((q : ℝ)) =
        (∑ k ∈ Finset.range 41,
          ((q : ℝ) / 2) ^ (n + 2 * k) / ((k.factorial : ℝ) * ((n + k).factorial : ℝ)))
          + ∑' i : ℕ, ((q : ℝ) / 2) ^ (n + 2 * (i + 41))
              / (((i + 41).factorial : ℝ) * ((n + (i + 41)).factorial : ℝ)) :=
      (sum_add_tsum_nat_add 41 hTsum).symm
    have htail_le : ∑' i : ℕ, ((q : ℝ) / 2) ^ (n + 2 * (i + 41))
            / (((i + 41).factorial : ℝ) * ((n + (i + 41)).factorial : ℝ))
          ≤ ((besselIn_error n q 40 : ℚ) : ℝ) := by
      rw [hcast_error]
      simpa using besseln_tail₇_local n (q : ℝ) 40 hqR.le (by exact_mod_cast hr1Q)
    calc besselI_series n ((q : ℝ))
        = _ + _ := hsplit
      _ ≤ _ + ((besselIn_error n q 40 : ℚ) : ℝ) := add_le_add_left htail_le _
      _ = ((besselIn_partial n q 40 : ℚ) : ℝ) + ((besselIn_error n q 40 : ℚ) : ℝ) := by
            rw [hcast_partial]
      _ = _ := by rw [Rat.cast_add]

private lemma seven_err_le_I0 (n : ℕ) :
    besselIn_error n (β₇_rat / 3) 40 ≤ besselI0_error (β₇_rat / 3) 40 := by
  set x : ℚ := β₇_rat / 3
  have hF1 : (0 : ℚ) < ((40 + 1).factorial : ℚ) := by positivity
  have hDr0 : (0 : ℚ) < 1 - (x / 2) ^ 2 / ((40 : ℕ) + 2 : ℚ) := by norm_num [β₇_rat]
  have hDle : 1 - (x / 2) ^ 2 / ((40 : ℕ) + 2 : ℚ)
      ≤ 1 - (x / 2) ^ 2 / ((n : ℚ) + (40 : ℕ) + 2) := by
    apply sub_le_sub_left
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by push_cast; linarith)
  have hpow : (x / 2) ^ (n + 2 * (40 + 1)) ≤ (x / 2) ^ (2 * 40 + 2) := by
    rw [show n + 2 * 41 = (2 * 40 + 2) + n from by omega, pow_add]
    calc (x / 2) ^ (2 * 40 + 2) * (x / 2) ^ n
        ≤ (x / 2) ^ (2 * 40 + 2) * 1 :=
          mul_le_mul_of_nonneg_left
            (pow_le_one n seven_q_half_nn seven_q_half_le1) (pow_nonneg seven_q_half_nn _)
      _ = _ := mul_one _
  have hfacN : ((40 + 1).factorial : ℚ) ≤ ((n + (40 + 1)).factorial : ℚ) :=
    by exact_mod_cast Nat.factorial_le (Nat.le_add_left (40 + 1) n)
  unfold besselIn_error besselI0_error
  refine le_trans (div_le_div_of_nonneg_left ?_ hDr0 hDle) ?_
  · exact div_nonneg (pow_nonneg seven_q_half_nn _) (by positivity)
  · exact (div_le_div_right hDr0).mpr
      (div_le_div (pow_nonneg seven_q_half_nn _) hpow (mul_pos hF1 hF1)
        (mul_le_mul_of_nonneg_left hfacN hF1.le))

theorem besselIn_seven_lo_nonneg (n : ℕ) : 0 ≤ (besselIn_seven_interval n).lo := by
  rw [seven_lo_eq]; unfold besselIn_partial
  apply Finset.sum_nonneg; intro k _
  exact div_nonneg (pow_nonneg (div_nonneg seven_q_pos.le (by norm_num)) _) (by positivity)

theorem besselIn_seven_hi_le (n : ℕ) : (besselIn_seven_interval n).hi ≤ 42 := by
  rw [seven_hi_eq]
  have hp : besselIn_partial n (β₇_rat / 3) 40 ≤ 41 := by
    unfold besselIn_partial
    have hbnd : ∑ k ∈ Finset.range 41,
        (β₇_rat / 3 / 2) ^ (n + 2 * k) /
          ((k.factorial : ℚ) * ((n + k).factorial : ℚ)) ≤
        ∑ _ ∈ Finset.range 41, (1 : ℚ) := by
      apply Finset.sum_le_sum; intro k _
      rw [div_le_one (by positivity)]
      calc (β₇_rat / 3 / 2) ^ (n + 2 * k)
          ≤ 1 ^ (n + 2 * k) := pow_le_pow_left seven_q_half_nn seven_q_half_le1 _
        _ = 1 := one_pow _
        _ ≤ ((k.factorial : ℚ) * ((n + k).factorial : ℚ)) :=
            by exact_mod_cast Nat.one_le_iff_ne_zero.mpr
              (Nat.mul_ne_zero (Nat.factorial_ne_zero k) (Nat.factorial_ne_zero _))
    linarith [hbnd, show ∑ _ ∈ Finset.range 41, (1 : ℚ) = 41 from by simp]
  have he : besselIn_error n (β₇_rat / 3) 40 ≤ 1 :=
    le_trans (seven_err_le_I0 n)
      (by norm_num [besselI0_error, β₇_rat, Nat.factorial])
  linarith

/-! ## §7  Toeplitz det interval for β₇ -/

def toeplitzDetInterval₇ (k : ℤ) : RatInterval :=
  detI (fun i j => besselIn_seven_interval (((i : ℤ) - j - k).natAbs))

theorem toeplitz_det₇_contains (k : ℤ) :
    (toeplitzDetInterval₇ k).contains ((toeplitzReal βR₇ k).det) := by
  apply detI_contains; intro i j
  simp only [toeplitzReal, Matrix.of_apply]
  have : βR₇ / 3 = ((β₇_rat / 3 : ℚ) : ℝ) := by push_cast; ring
  rw [this]; exact besselIn_seven_contains _

/-! ## §8  Rational constants (11-term window, Icc(-5,5)) -/

/-- Upper bound for ∑_{k=-5}^{5} det(T_k(β₇)). -/
def finite_7_hi_sum : ℚ :=
  ∑ i ∈ Finset.range 11, (toeplitzDetInterval₇ ((i : ℤ) - 5)).hi

/-- Tail bound: 2·6·C₇³·q₇⁴·(1-q₇)⁻¹
    ≤ 2·6·(3/2)³·(1/8)⁴·(8/7) = 2·81/7168·(8/7)... actually:
    2·(6·(3/2)³·(1/8)⁴·8/7) = 2·(81/4·1/4096·8/7) = 2·81/(7·2048) = 162/14336 = 81/7168 ≤ 3/200. -/
def tail_7_ub : ℚ := 3 / 200

/-! ## §9  natAbs at complement elements (offset 6) -/

private lemma natAbs₇_pos (n : ℕ) : (↑n + 6 : ℤ).natAbs = n + 6 := by
  rw [show (↑n + 6 : ℤ) = ↑(n + 6 : ℕ) from by push_cast; ring]
  exact Int.natAbs_ofNat _

private lemma natAbs₇_neg (n : ℕ) : (-(↑n + 6 : ℤ)).natAbs = n + 6 := by
  rw [Int.natAbs_neg]; exact natAbs₇_pos n

-- g₇(n+6) = 6·C₇³·q₇^(6-2)·q₇^n = 6·C₇³·q₇^4·q₇^n
private lemma g₇_pos_eq (n : ℕ) :
    g₇ (↑n + 6 : ℤ) = 6 * C_exp₇ ^ 3 * q₇ ^ 4 * q₇ ^ n := by
  unfold g₇; rw [natAbs₇_pos, show n + 6 - 2 = n + 4 from by omega, pow_add]; ring

private lemma g₇_neg_eq (n : ℕ) :
    g₇ (-(↑n + 6) : ℤ) = 6 * C_exp₇ ^ 3 * q₇ ^ 4 * q₇ ^ n := by
  unfold g₇; rw [natAbs₇_neg, show n + 6 - 2 = n + 4 from by omega, pow_add]; ring

/-! ## §10  ℕ-bijections for complement halves -/

private def posEquiv₇ : ℕ ≃ {k : ℤ | k ≥ 6} where
  toFun n := ⟨↑n + 6, by simp only [Set.mem_setOf_eq]; omega⟩
  invFun k := (k.val - 6).toNat
  left_inv n := by simp only; omega
  right_inv := fun ⟨k, hk⟩ => by
    simp only [Set.mem_setOf_eq] at hk; apply Subtype.ext; simp only; omega

private def negEquiv₇ : ℕ ≃ {k : ℤ | k ≤ -6} where
  toFun n := ⟨-(↑n + 6), by simp only [Set.mem_setOf_eq]; omega⟩
  invFun k := (-k.val - 6).toNat
  left_inv n := by simp only; omega
  right_inv := fun ⟨k, hk⟩ => by
    simp only [Set.mem_setOf_eq] at hk; apply Subtype.ext; simp only; omega

private lemma compl_S6k7_eq :
    (↑S6k7 : Set ℤ)ᶜ = {k : ℤ | k ≥ 6} ∪ {k : ℤ | k ≤ -6} := by
  ext k; simp only [Set.mem_compl_iff, Finset.mem_coe, S6k7, Finset.mem_Icc,
    Set.mem_union, Set.mem_setOf_eq, not_and_or, not_le]; omega

/-! ## §11  Tail bound ∑'_{compl} g₇ ≤ 3/200 -/

private lemma compl_g₇_tsum_le :
    ∑' k : ↥((↑S6k7 : Set ℤ))ᶜ, g₇ (k : ℤ) ≤ (tail_7_ub : ℝ) := by
  rw [compl_S6k7_eq]
  have hdisj : Disjoint {k : ℤ | k ≥ 6} {k : ℤ | k ≤ -6} :=
    Set.disjoint_left.mpr fun k h1 h2 => by
      simp only [Set.mem_setOf_eq] at h1 h2; omega
  rw [tsum_union_disjoint hdisj (g₇_summable.subtype _) (g₇_summable.subtype _)]
  have hpos_idx : ∑' k : {k : ℤ | k ≥ 6}, g₇ k.val = ∑' n : ℕ, g₇ (↑n + 6 : ℤ) :=
    ((Equiv.tsum_eq posEquiv₇ (fun k : {k : ℤ | k ≥ 6} => g₇ k.val)).symm).trans
      (by simp only [posEquiv₇, Equiv.coe_fn_mk])
  have hneg_idx : ∑' k : {k : ℤ | k ≤ -6}, g₇ k.val = ∑' n : ℕ, g₇ (-(↑n + 6) : ℤ) :=
    ((Equiv.tsum_eq negEquiv₇ (fun k : {k : ℤ | k ≤ -6} => g₇ k.val)).symm).trans
      (by simp only [negEquiv₇, Equiv.coe_fn_mk])
  rw [hpos_idx, hneg_idx]
  simp_rw [g₇_pos_eq, g₇_neg_eq]
  have hgeo : ∑' n : ℕ, 6 * C_exp₇ ^ 3 * q₇ ^ 4 * q₇ ^ n =
      6 * C_exp₇ ^ 3 * q₇ ^ 4 * (1 - q₇)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one q₇_nonneg q₇_lt_one]
  rw [hgeo, hgeo]
  have hC3 : C_exp₇ ^ 3 ≤ (3 / 2 : ℝ) ^ 3 :=
    pow_le_pow_left C_exp₇_nonneg C_exp₇_lt_three_halves.le 3
  have hq4 : q₇ ^ 4 ≤ (1 / 8 : ℝ) ^ 4 :=
    pow_le_pow_left q₇_nonneg q₇_lt_eighth.le 4
  have hq_pos : (0 : ℝ) < 1 - q₇ := by linarith [q₇_lt_one]
  have h_lhs : 6 * C_exp₇ ^ 3 * q₇ ^ 4 ≤ 6 * (3 / 2 : ℝ) ^ 3 * (1 / 8 : ℝ) ^ 4 := by
    nlinarith [mul_le_mul hC3 hq4 (pow_nonneg q₇_nonneg 4)
      (by positivity : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ 3)]
  have h_each : 6 * C_exp₇ ^ 3 * q₇ ^ 4 * (1 - q₇)⁻¹ ≤
      6 * (3 / 2 : ℝ) ^ 3 * (1 / 8 : ℝ) ^ 4 * (8 / 7) :=
    mul_le_mul h_lhs inv_one_sub_q₇_le (inv_nonneg.mpr hq_pos.le) (by positivity)
  simp only [tail_7_ub]
  linarith [show 2 * (6 * (3 / 2 : ℝ) ^ 3 * (1 / 8 : ℝ) ^ 4 * (8 / 7)) ≤ 3 / 200 from by
    norm_num]

/-! ## §12  Tail det bound, tsum split, finite sum bound -/

private lemma tail₇_le_ub :
    ∑' k : ↥((↑S6k7 : Set ℤ))ᶜ, (toeplitzReal βR₇ (k : ℤ)).det ≤ (tail_7_ub : ℝ) :=
  le_trans
    (tsum_le_tsum (fun k => le_trans (le_abs_self _) (det_abs₇_le k.val))
      (summable_toeplitz_det₇.subtype _) (g₇_summable.subtype _))
    compl_g₇_tsum_le

private lemma tsum₇_det_split :
    ∑' k : ℤ, (toeplitzReal βR₇ k).det =
    ∑ k ∈ S6k7, (toeplitzReal βR₇ k).det +
    ∑' k : ↥((↑S6k7 : Set ℤ))ᶜ, (toeplitzReal βR₇ (k : ℤ)).det :=
  (sum_add_tsum_compl (s := S6k7) summable_toeplitz_det₇).symm

private lemma finite₇_sum_le :
    ∑ i ∈ Finset.range 11, (toeplitzReal βR₇ ((i : ℤ) - 5)).det ≤
    (finite_7_hi_sum : ℝ) := by
  apply le_trans (Finset.sum_le_sum (fun i _ => (toeplitz_det₇_contains ((i : ℤ) - 5)).2))
  simp only [finite_7_hi_sum]; push_cast; rfl

/-! ## §13  Part (b): ∑' det ≤ finite_7_hi_sum + tail_7_ub -/

theorem seven_tsum_det_le :
    ∑' k : ℤ, (toeplitzReal βR₇ k).det ≤ (↑finite_7_hi_sum + ↑tail_7_ub : ℝ) := by
  rw [tsum₇_det_split]
  have h_finite : ∑ k ∈ S6k7, (toeplitzReal βR₇ k).det ≤ (↑finite_7_hi_sum : ℝ) := by
    have h_reindex : ∑ k ∈ S6k7, (toeplitzReal βR₇ k).det =
        ∑ i ∈ Finset.range 11, (toeplitzReal βR₇ ((i : ℤ) - 5)).det := by
      apply Finset.sum_nbij (fun i => (i : ℤ) - 5)
      · intro i hi
        simp only [S6k7, Finset.mem_Icc]
        simp only [Finset.mem_range] at hi; omega
      · intro i₁ _ i₂ _ h; omega
      · intro k hk
        simp only [S6k7, Finset.mem_Icc] at hk
        exact ⟨(k + 5).toNat, by simp only [Finset.mem_range]; omega, by omega⟩
      · intro i _; rfl
    rw [h_reindex]; exact finite₇_sum_le
  linarith [tail₇_le_ub]

/-! ## §14  Part (c): pure ℚ inequality -/

/-- P₂₈(β₇) · (finite_7_hi_sum + tail_7_ub) < 1/7 — pure ℚ.
    Margin: 1/7 − P₂₈·(F+T) ≈ 0.0124.
    Numerics: P₂₈(11/5) ≈ 0.11080, F ≈ 1.1621, T = 3/200 = 0.015.
    0.11080 × 1.177 ≈ 0.1304 < 0.1429 = 1/7.
    Denominator ≈ 10^818 digits — comparable to kp case (10^460); decide works. -/
set_option maxHeartbeats 400000000 in
theorem seven_part_c :
    exp_neg_partial β₇_rat 28 * (finite_7_hi_sum + tail_7_ub) < 1 / 7 := by
  norm_num [exp_neg_partial, β₇_rat, finite_7_hi_sum, tail_7_ub,
            toeplitzDetInterval₇, detI, besselIn_seven_interval, besselIn_interval,
            ofRat, RatInterval.hi, RatInterval.lo,
            Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

/-! ## §15  Main theorem -/

/-- **w1_weyl_series(β₇) < 1/7** — classical trio only, 0 gaps.
    β₇ = 11/5 = 2.20. D4 threshold: w1(β) < 1/7 for all β ≥ 2.20. -/
theorem w1_seven_lt : w1_weyl_series βR₇ < 1 / 7 := by
  have hQ : (exp_neg_partial β₇_rat 28 : ℝ) * (↑finite_7_hi_sum + ↑tail_7_ub) < 1 / 7 :=
    by exact_mod_cast seven_part_c
  have hexp : Real.exp (-βR₇) ≤ ((exp_neg_partial β₇_rat 28 : ℚ) : ℝ) := exp₇_upper
  have hdet_le := seven_tsum_det_le
  unfold w1_weyl_series
  rcases le_or_lt 0 (∑' k : ℤ, (toeplitzReal βR₇ k).det) with hnn | hneg
  · have hFT_nn : (0 : ℝ) ≤ ↑finite_7_hi_sum + ↑tail_7_ub := le_trans hnn hdet_le
    calc Real.exp (-βR₇) * ∑' k : ℤ, (toeplitzReal βR₇ k).det
        ≤ Real.exp (-βR₇) * (↑finite_7_hi_sum + ↑tail_7_ub) :=
            mul_le_mul_of_nonneg_left hdet_le (Real.exp_pos _).le
      _ ≤ (exp_neg_partial β₇_rat 28 : ℝ) * (↑finite_7_hi_sum + ↑tail_7_ub) :=
            mul_le_mul_of_nonneg_right hexp hFT_nn
      _ < 1 / 7 := hQ
  · linarith [mul_neg_of_pos_of_neg (Real.exp_pos (-βR₇)) hneg]

/-- Connection: 2.20 = 11/5 = β₇_rat as a real. -/
theorem beta0_seven_eq_rat : (2.20 : ℝ) = βR₇ := by norm_num [β₇_rat]


/-! ## §16  Lower bound: w1_weyl_series(β₇) > 1/8 > 0

    Method (Route 1 — Bessel lower-enclosure):
      1. exp₇_lower : P₂₈ - err₂₈ ≤ exp(-β₇)
         (same Taylor-Lagrange machinery as exp₇_upper; remainder R₂₉ < 0
          and |R₂₉| = exp(-ξ)·β₇²⁹/29! < β₇²⁹/29! = err₂₈ since exp(-ξ) < 1)
      2. seven_tsum_det_ge : finite_7_lo_sum - tail_ub ≤ ∑' det
         (lower Bessel enclosure: besselIn_seven_interval .lo side)
      3. seven_lo_part_c : (P₂₈-err₂₈)·(finite_lo-tail_ub) > 1/8  [decide]
      4. w1_seven_gt_eighth : 1/8 < w1_weyl_series β₇
      5. w1_seven_pos   : 0 < w1_weyl_series β₇     closes w1_seven_pos_Surface
-/

/-- Lower end of the Lagrange bracket `[P₂₈ - err₂₈, P₂₈]` for `exp(-β₇)`.
    Dual of `exp₇_upper`: same `taylor_mean_remainder_lagrange` step.
    Remainder R₂₉ = (-1)²⁹·exp(-x')·β₇²⁹/29! = -exp(-x')·β₇²⁹/29! ∈ (-err₂₈, 0)
    because 0 < exp(-x') < 1 for x' ∈ (0, β₇).
    Hence exp(-β₇) = P₂₈ - R₂₉ > P₂₈ - err₂₈. -/
private theorem exp₇_lower :
    ((exp_neg_partial β₇_rat 28 - exp_neg_error β₇_rat 28 : ℚ) : ℝ) ≤ Real.exp (-βR₇) := by
  have hpos : (0 : ℝ) < βR₇ := by norm_num [β₇_rat]
  have hcd  : ContDiffOn ℝ 28 (fun t : ℝ => Real.exp (-t)) (Set.Icc 0 βR₇) := by fun_prop
  have hcd' : ContDiffOn ℝ (29 : ℕ∞) (fun t : ℝ => Real.exp (-t)) (Set.Icc 0 βR₇) := by fun_prop
  have hdiff : DifferentiableOn ℝ
      (iteratedDerivWithin 28 (fun t : ℝ => Real.exp (-t)) (Set.Icc 0 βR₇)) (Set.Ioo 0 βR₇) :=
    (hcd'.differentiableOn_iteratedDerivWithin (by norm_num : (28 : ℕ∞) < 29)
      (uniqueDiffOn_Icc hpos)).mono Set.Ioo_subset_Icc_self
  obtain ⟨x', hx'mem, hrem⟩ := taylor_mean_remainder_lagrange hpos hcd hdiff
  rw [seven_iterDeriv 29 x' (Set.Ioo_subset_Icc_self hx'mem), seven_taylorPoly_eq] at hrem
  have hexp_le1 : Real.exp (-x') ≤ 1 :=
    le_of_lt (Real.exp_lt_one_iff.mpr (by linarith [hx'mem.1]))
  have hβ29_nn : (0 : ℝ) ≤ βR₇ ^ 29 / ((29 : ℝ).factorial) :=
    le_of_lt (div_pos (pow_pos hpos 29) (by exact_mod_cast Nat.factorial_pos 29))
  have herr : ((exp_neg_error β₇_rat 28 : ℚ) : ℝ) = βR₇ ^ 29 / ((29 : ℝ).factorial) := by
    unfold exp_neg_error; push_cast; ring
  rw [Rat.cast_sub, herr]
  nlinarith [show ((-1 : ℝ) ^ 29) = -1 from by norm_num,
             mul_le_mul_of_nonneg_right hexp_le1 hβ29_nn]

/-- Rational lower bound for the window sum `∑_{k=-5}^{5} det(T_k(β₇))`. -/
def finite_7_lo_sum : ℚ :=
  ∑ i ∈ Finset.range 11, (toeplitzDetInterval₇ ((i : ℤ) - 5)).lo

/-- Tail lower bound: the complement tsum ≥ -tail_7_ub.
    Follows from |tail det| ≤ |tail g₇| ≤ tail_7_ub via det_abs₇_le. -/
private lemma tail₇_ge_lb :
    -(tail_7_ub : ℝ) ≤
      ∑' k : ↥((↑S6k7 : Set ℤ))ᶜ, (toeplitzReal βR₇ (k : ℤ)).det := by
  have hs : Summable (fun k : ↥((↑S6k7 : Set ℤ))ᶜ => (toeplitzReal βR₇ k.val).det) :=
    summable_toeplitz_det₇.subtype _
  have hUB : -(∑' k : ↥((↑S6k7 : Set ℤ))ᶜ, (toeplitzReal βR₇ k.val).det) ≤
      (tail_7_ub : ℝ) := by
    rw [← tsum_neg hs]
    exact le_trans
      (tsum_le_tsum
        (fun k => calc -(toeplitzReal βR₇ k.val).det
            ≤ |-(toeplitzReal βR₇ k.val).det| := le_abs_self _
          _ = |(toeplitzReal βR₇ k.val).det| := abs_neg _
          _ ≤ g₇ k.val := det_abs₇_le k.val)
        hs.neg (g₇_summable.subtype _))
      compl_g₇_tsum_le
  linarith

/-- Lower bound: finite_7_lo_sum - tail_7_ub ≤ ∑' det. -/
theorem seven_tsum_det_ge :
    (↑finite_7_lo_sum - ↑tail_7_ub : ℝ) ≤ ∑' k : ℤ, (toeplitzReal βR₇ k).det := by
  rw [tsum₇_det_split]
  have h_reindex : ∑ k ∈ S6k7, (toeplitzReal βR₇ k).det =
      ∑ i ∈ Finset.range 11, (toeplitzReal βR₇ ((i : ℤ) - 5)).det := by
    apply Finset.sum_nbij (fun i => (i : ℤ) - 5)
    · intro i hi
      simp only [S6k7, Finset.mem_Icc]
      simp only [Finset.mem_range] at hi; omega
    · intro i₁ _ i₂ _ h; omega
    · intro k hk
      simp only [S6k7, Finset.mem_Icc] at hk
      exact ⟨(k + 5).toNat, by simp only [Finset.mem_range]; omega, by omega⟩
    · intro i _; rfl
  have h_finite : (finite_7_lo_sum : ℝ) ≤ ∑ k ∈ S6k7, (toeplitzReal βR₇ k).det := by
    rw [h_reindex]
    calc (finite_7_lo_sum : ℝ)
        = (↑(∑ i ∈ Finset.range 11, (toeplitzDetInterval₇ ((i : ℤ) - 5)).lo) : ℝ) := by
              simp [finite_7_lo_sum]
      _ = ∑ i ∈ Finset.range 11,
            ((toeplitzDetInterval₇ ((i : ℤ) - 5)).lo : ℝ) := by push_cast; rfl
      _ ≤ ∑ i ∈ Finset.range 11, (toeplitzReal βR₇ ((i : ℤ) - 5)).det :=
              Finset.sum_le_sum (fun i _ => (toeplitz_det₇_contains ((i : ℤ) - 5)).1)
  linarith [tail₇_ge_lb]

/-- Pure ℚ: (P₂₈ - err₂₈) · (finite_7_lo_sum - tail_7_ub) > 1/8.
    Numerics: P₂₈(11/5) - err₂₈ ≈ 0.11080; window lo ≈ 1.189; tail = 3/200.
    Product ≈ 0.11080 × 1.174 ≈ 0.1301 > 0.125 = 1/8. Margin ≈ 0.0051.
    Denominator complexity comparable to seven_part_c. -/
set_option maxHeartbeats 400000000 in
theorem seven_lo_part_c :
    (exp_neg_partial β₇_rat 28 - exp_neg_error β₇_rat 28) *
      (finite_7_lo_sum - tail_7_ub) > 1 / 8 := by
  norm_num [exp_neg_partial, exp_neg_error, β₇_rat, finite_7_lo_sum, tail_7_ub,
            toeplitzDetInterval₇, detI, besselIn_seven_interval, besselIn_interval,
            ofRat, RatInterval.lo, RatInterval.hi,
            Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

/-- **w1_weyl_series(β₇) > 1/8** — positivity via the Lagrange lower bracket. -/
theorem w1_seven_gt_eighth : 1 / 8 < w1_weyl_series βR₇ := by
  have hQ : (1 : ℝ) / 8 <
      ((exp_neg_partial β₇_rat 28 - exp_neg_error β₇_rat 28 : ℚ) : ℝ) *
        (↑finite_7_lo_sum - ↑tail_7_ub) := by exact_mod_cast seven_lo_part_c
  have hFT_nn : (0 : ℝ) ≤ ↑finite_7_lo_sum - ↑tail_7_ub := by
    have : (0 : ℚ) < finite_7_lo_sum - tail_7_ub := by
      norm_num [finite_7_lo_sum, tail_7_ub, toeplitzDetInterval₇, detI,
                besselIn_seven_interval, besselIn_interval, ofRat, RatInterval.lo,
                Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    exact_mod_cast this.le
  unfold w1_weyl_series
  calc 1 / 8
      < ((exp_neg_partial β₇_rat 28 - exp_neg_error β₇_rat 28 : ℚ) : ℝ) *
            (↑finite_7_lo_sum - ↑tail_7_ub) := hQ
    _ ≤ Real.exp (-βR₇) * (↑finite_7_lo_sum - ↑tail_7_ub) :=
          mul_le_mul_of_nonneg_right exp₇_lower hFT_nn
    _ ≤ Real.exp (-βR₇) * ∑' k : ℤ, (toeplitzReal βR₇ k).det :=
          mul_le_mul_of_nonneg_left seven_tsum_det_ge (Real.exp_pos _).le

/-- **0 < w1_weyl_series(β₇)** — closes w1_seven_pos_Surface.
    Classical trio only. 0 sorry. 0 new axioms. -/
theorem w1_seven_pos : 0 < w1_weyl_series βR₇ :=
  lt_trans (by norm_num) w1_seven_gt_eighth

end TheoremaAureum.Towers.YM.W1SeventhProof

-- #print axioms TheoremaAureum.Towers.YM.W1SeventhProof.w1_seven_lt
-- Expected: [propext, Classical.choice, Quot.sound]
