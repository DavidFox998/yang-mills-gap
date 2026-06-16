-- Axiom status: Classical trio only. 0 gaps. 0 new axioms.
-- PROVES: w1_weyl_series (30029/6250 : ℝ) < 1/56
-- CLOSES: W1_KP_Surface in KP_Closure.lean (beta0_kp_star = 4.80464 = 30029/6250).
-- Mirror of BesselBounds.lean + W1NumericProof.lean adapted for β_kp = 30029/6250.
--
-- Numeric summary (β_kp ≈ 4.805):
--   r_kp = β_kp/6 ≈ 0.8008  (<1, NOT <1/2)
--   q_kp = r_kp^3 ≈ 0.513   (<1, NOT ≤1/8; use q_kp < 729/1331)
--   C_exp_kp = exp(r_kp^2) ≈ 1.899  (< 3, NOT <3/2)
--   exp(-β_kp) ≈ 0.00816
--   Tail bound: 2·6·3³·(729/1331)²⁴·(1331/602) ≈ 3.8e-4 ≤ 1/100 = tail_kp_ub
--   Part(c): P_28(β_kp) · (finite_kp_hi_sum + 1/100) < 1/56  [decide]

import Towers.YM.BesselBounds

namespace TheoremaAureum.Towers.YM.KPW1Proof

open Real BigOperators Finset
open TheoremaAureum.Towers.YM.WeylToeplitzBound
open TheoremaAureum.Towers.YM.IntervalArith
open TheoremaAureum.Towers.YM.BesselSeries RatInterval

/-! ## §0  KP constants -/

/-- β_kp = 30029/6250 = 4.80464 exactly. -/
def β_kp_rat : ℚ := 30029 / 6250

private local notation "βR" => (β_kp_rat : ℝ)
private abbrev S26kp : Finset ℤ := Finset.Icc (-25) 25

/-! ## §1  Decay constants -/

noncomputable def r_kp : ℝ := βR / 6
noncomputable def q_kp : ℝ := r_kp ^ 3
noncomputable def C_exp_kp : ℝ := Real.exp (r_kp ^ 2)

private lemma r_kp_pos : 0 < r_kp := by norm_num [r_kp, β_kp_rat]
private lemma r_kp_nonneg : 0 ≤ r_kp := r_kp_pos.le
-- r_kp = 30029/37500 ≈ 0.8008 < 1 (NOT < 1/2)
private lemma r_kp_lt_one : r_kp < 1 := by unfold r_kp; norm_num [β_kp_rat]
private lemma q_kp_pos : 0 < q_kp := pow_pos r_kp_pos 3
private lemma q_kp_nonneg : 0 ≤ q_kp := q_kp_pos.le
private lemma q_kp_lt_one : q_kp < 1 :=
  pow_lt_one r_kp_nonneg r_kp_lt_one (by norm_num)
private lemma C_exp_kp_pos : 0 < C_exp_kp := Real.exp_pos _
private lemma C_exp_kp_nonneg : 0 ≤ C_exp_kp := C_exp_kp_pos.le

-- r_kp = 30029/37500 < 9/11  [cross-mult: 30029*11 = 330319 < 37500*9 = 337500]
private lemma r_kp_lt_nine_elevenths : r_kp < 9 / 11 := by
  unfold r_kp; norm_num [β_kp_rat]

-- q_kp = r_kp^3 < (9/11)^3 = 729/1331
private lemma q_kp_lt_729_1331 : q_kp < 729 / 1331 := by
  unfold q_kp
  calc r_kp ^ 3 < (9 / 11 : ℝ) ^ 3 :=
        pow_lt_pow_left r_kp_nonneg r_kp_lt_nine_elevenths 3
    _ = 729 / 1331 := by norm_num

-- C_exp_kp = exp(r_kp^2) < exp(1) < 3
private lemma C_exp_kp_lt_three : C_exp_kp < 3 := by
  unfold C_exp_kp
  have hr_sq : r_kp ^ 2 < 1 := by nlinarith [r_kp_lt_one, r_kp_nonneg]
  have h1 : Real.exp (r_kp ^ 2) < Real.exp 1 := Real.exp_lt_exp.mpr hr_sq
  linarith [Real.exp_one_lt_d9]

-- (1 - q_kp)^{-1} ≤ 1331/602  [since q_kp < 729/1331, so 1-q_kp > 602/1331]
private lemma inv_one_sub_q_kp_le : (1 - q_kp)⁻¹ ≤ 1331 / 602 := by
  rw [show (1331 : ℝ) / 602 = ((602 : ℝ) / 1331)⁻¹ from by norm_num]
  apply inv_le_inv_of_le (by norm_num : (0 : ℝ) < 602 / 1331)
  linarith [q_kp_lt_729_1331]

/-! ## §2  Entry bounds -/

private lemma entry_kp_nonneg (k : ℤ) (i j : Fin 3) :
    0 ≤ (toeplitzReal βR k) i j := by
  simp only [toeplitzReal, Matrix.of_apply]
  apply tsum_nonneg; intro n
  exact div_nonneg (pow_nonneg (div_nonneg (by norm_num [β_kp_rat]) two_pos.le) _) (by positivity)

private lemma entry_kp_le_pow_mul (k : ℤ) (i j : Fin 3) :
    (toeplitzReal βR k) i j ≤ r_kp ^ ((i : ℤ) - j - k).natAbs * C_exp_kp := by
  simp only [toeplitzReal, Matrix.of_apply]
  apply le_trans (besselI_series_le_exp_bound _ _ (by norm_num [β_kp_rat]))
  have hr : βR / 3 / 2 = r_kp := by unfold r_kp; ring
  simp only [hr, C_exp_kp]
  exact le_refl _

private lemma index_kp_lower (k : ℤ) (i j : Fin 3) :
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

private lemma entry_kp_le_geometric (k : ℤ) (i j : Fin 3) :
    (toeplitzReal βR k) i j ≤ r_kp ^ (k.natAbs - 2) * C_exp_kp :=
  le_trans (entry_kp_le_pow_mul k i j)
    (by gcongr; exact r_kp_lt_one.le; exact index_kp_lower k i j)

/-! ## §3  Det absolute-value bound -/

noncomputable def g_kp (k : ℤ) : ℝ := 6 * C_exp_kp ^ 3 * q_kp ^ (k.natAbs - 2)

private lemma g_kp_nonneg (k : ℤ) : 0 ≤ g_kp k :=
  mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg C_exp_kp_nonneg 3)) (pow_nonneg q_kp_nonneg _)

private lemma det_abs_kp_le (k : ℤ) : |(toeplitzReal βR k).det| ≤ g_kp k := by
  set b := r_kp ^ (k.natAbs - 2) * C_exp_kp with hb_def
  have hb : 0 ≤ b := mul_nonneg (pow_nonneg r_kp_nonneg _) C_exp_kp_nonneg
  have hM : ∀ i j : Fin 3, (toeplitzReal βR k) i j ≤ b := entry_kp_le_geometric k
  have hM0 : ∀ i j : Fin 3, 0 ≤ (toeplitzReal βR k) i j := entry_kp_nonneg k
  have hprod : ∀ a₁ a₂ a₃ : ℝ,
      0 ≤ a₁ → a₁ ≤ b → 0 ≤ a₂ → a₂ ≤ b → 0 ≤ a₃ → a₃ ≤ b → a₁ * a₂ * a₃ ≤ b ^ 3 :=
    fun a₁ a₂ a₃ h1 h1b h2 h2b h3 h3b => by
      nlinarith [mul_nonneg h1 h2, show b ^ 3 = b * b * b from by ring]
  have hgb : g_kp k = 6 * b ^ 3 := by
    unfold g_kp q_kp b
    rw [mul_pow, ← pow_mul, show (k.natAbs - 2) * 3 = 3 * (k.natAbs - 2) from mul_comm _ _, pow_mul]
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

/-! ## §4  Summability of g_kp and det series -/

-- Summability of k ↦ q_kp^k.natAbs on ℤ (needed for g_kp_summable).
private lemma kp_natAbs_summable : Summable (fun k : ℤ => q_kp ^ k.natAbs) := by
  apply (Int.summable_iff).mpr
  exact ⟨by simp_rw [Function.comp, Int.natAbs_ofNat]
             exact summable_geometric_of_lt_one q_kp_nonneg q_kp_lt_one,
         by simp_rw [Int.natAbs_negSucc, pow_succ]
            exact (summable_geometric_of_lt_one q_kp_nonneg q_kp_lt_one).mul_left q_kp⟩

lemma g_kp_summable : Summable g_kp := by
  -- g_kp k = 6*C_exp_kp^3 * q_kp^(k.natAbs-2) ≤ (6*C_exp_kp^3/q_kp^2) * q_kp^k.natAbs
  apply Summable.of_nonneg_of_le g_kp_nonneg _
    (kp_natAbs_summable.mul_left (6 * C_exp_kp ^ 3 / q_kp ^ 2))
  intro k
  unfold g_kp
  rw [show 6 * C_exp_kp ^ 3 / q_kp ^ 2 * q_kp ^ k.natAbs =
        6 * C_exp_kp ^ 3 * (q_kp ^ k.natAbs / q_kp ^ 2) from by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [le_div_iff (pow_pos q_kp_pos 2)]
  rcases le_or_lt k.natAbs 2 with h | h
  · simp only [Nat.sub_eq_zero_of_le h, pow_zero, one_mul]
    exact pow_le_pow_of_le_one q_kp_nonneg q_kp_lt_one.le h
  · have hn : k.natAbs - 2 + 2 = k.natAbs := Nat.sub_add_cancel (by omega)
    rw [← pow_add, hn]

theorem summable_toeplitz_det_kp :
    Summable (fun k : ℤ => (toeplitzReal βR k).det) := by
  apply Summable.of_norm_bounded g_kp g_kp_summable
  intro k
  rw [Real.norm_eq_abs]
  exact det_abs_kp_le k

/-! ## §5  Exp upper bound via Taylor-Lagrange (N=28, even) -/

private theorem kp_iterDeriv (n : ℕ) :
    ∀ t ∈ Set.Icc (0 : ℝ) βR,
      iteratedDerivWithin n (fun s => Real.exp (-s)) (Set.Icc 0 βR) t =
        (-1 : ℝ) ^ n * Real.exp (-t) := by
  have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) βR) :=
    uniqueDiffOn_Icc (by norm_num [β_kp_rat])
  induction n with
  | zero => intro t _; simp [iteratedDerivWithin_zero]
  | succ n ih =>
    intro t ht
    rw [iteratedDerivWithin_succ (hu t ht),
        derivWithin_congr (fun y hy => ih y hy) (ih t ht)]
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-t)) t := by
      have := (Real.hasDerivAt_exp (-t)).comp t ((hasDerivAt_id t).neg); simpa using this
    rw [(h1.const_mul ((-1 : ℝ) ^ n)).hasDerivWithinAt.derivWithin (hu t ht), pow_succ]; ring

private theorem kp_taylorPoly_eq :
    taylorWithinEval (fun t : ℝ => Real.exp (-t)) 28 (Set.Icc 0 βR) 0 βR =
      ((exp_neg_partial β_kp_rat 28 : ℚ) : ℝ) := by
  rw [taylor_within_apply, exp_neg_partial, Rat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) βR := ⟨le_refl _, by norm_num [β_kp_rat]⟩
  rw [kp_iterDeriv k 0 h0]
  simp only [neg_zero, Real.exp_zero, mul_one, sub_zero, smul_eq_mul]
  push_cast; ring

theorem exp_kp_upper : Real.exp (-βR) ≤ ((exp_neg_partial β_kp_rat 28 : ℚ) : ℝ) := by
  have hpos : (0 : ℝ) < βR := by norm_num [β_kp_rat]
  have hcd : ContDiffOn ℝ 28 (fun t : ℝ => Real.exp (-t)) (Set.Icc 0 βR) := by fun_prop
  have hcd' : ContDiffOn ℝ (29 : ℕ∞) (fun t : ℝ => Real.exp (-t)) (Set.Icc 0 βR) := by fun_prop
  have hdiff : DifferentiableOn ℝ
      (iteratedDerivWithin 28 (fun t : ℝ => Real.exp (-t)) (Set.Icc 0 βR)) (Set.Ioo 0 βR) :=
    (hcd'.differentiableOn_iteratedDerivWithin (by norm_num : (28 : ℕ∞) < 29)
      (uniqueDiffOn_Icc hpos)).mono Set.Ioo_subset_Icc_self
  obtain ⟨x', hx'mem, hrem⟩ := taylor_mean_remainder_lagrange hpos hcd hdiff
  rw [kp_iterDeriv 29 x' (Set.Ioo_subset_Icc_self hx'mem), kp_taylorPoly_eq] at hrem
  have hQpos : (0 : ℝ) < Real.exp (-x') * (βR ^ 29 / ((29 : ℝ).factorial)) :=
    mul_pos (Real.exp_pos _) (div_pos (pow_pos hpos 29) (by exact_mod_cast Nat.factorial_pos 29))
  nlinarith [show ((-1 : ℝ) ^ 29) = -1 from by norm_num]

/-! ## §6  Bessel enclosures for β_kp/3 -/

def besselIn_kp_interval (n : ℕ) : RatInterval :=
  besselIn_interval n (ofRat (β_kp_rat / 3)) 40

-- β_kp/3/2 = β_kp/6 = 30029/37500 ≈ 0.8008; note this is > 1/2 but ≤ 1
private lemma kp_q_pos : (0 : ℚ) < β_kp_rat / 3 := by norm_num [β_kp_rat]
private lemma kp_q_half_nn : (0 : ℚ) ≤ β_kp_rat / 3 / 2 := by norm_num [β_kp_rat]
private lemma kp_q_half_le1 : β_kp_rat / 3 / 2 ≤ 1 := by norm_num [β_kp_rat]
private lemma kp_r1Q (n : ℕ) : (β_kp_rat / 3 / 2) ^ 2 / ((n : ℚ) + 40 + 2) < 1 := by
  rw [div_lt_one (by positivity)]
  have : (β_kp_rat / 3 / 2) ^ 2 < 42 := by norm_num [β_kp_rat]
  push_cast; linarith [Nat.cast_nonneg (α := ℚ) n]

private lemma kp_err_nonneg (n : ℕ) : 0 ≤ besselIn_error n (β_kp_rat / 3) 40 := by
  unfold besselIn_error
  apply div_nonneg
  · exact div_nonneg (pow_nonneg (div_nonneg kp_q_pos.le (by norm_num)) _) (by positivity)
  · linarith [kp_r1Q n]

private lemma kp_lo_eq (n : ℕ) :
    (besselIn_kp_interval n).lo = besselIn_partial n (β_kp_rat / 3) 40 := by
  simp only [besselIn_kp_interval, besselIn_interval, ofRat]
  exact min_eq_left (le_add_of_nonneg_right (kp_err_nonneg n))

private lemma kp_hi_eq (n : ℕ) :
    (besselIn_kp_interval n).hi =
      besselIn_partial n (β_kp_rat / 3) 40 + besselIn_error n (β_kp_rat / 3) 40 := by
  simp only [besselIn_kp_interval, besselIn_interval, ofRat]
  exact max_eq_right (le_add_of_nonneg_right (kp_err_nonneg n))

-- Geometric Bessel tail bound (mirrors besseln_term_tail_le from IntervalBessel.lean).
private theorem besseln_tail_kp (n : ℕ) (y : ℝ) (N : ℕ) (hy : 0 ≤ y)
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

theorem besselIn_kp_contains (n : ℕ) :
    (besselIn_kp_interval n).contains (besselI_series n ((β_kp_rat / 3 : ℚ) : ℝ)) := by
  set q : ℚ := β_kp_rat / 3 with hq
  have hqpos : 0 < q := kp_q_pos
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hr1Q : (q / 2) ^ 2 / ((n : ℚ) + 40 + 2) < 1 := kp_r1Q n
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
  · rw [kp_lo_eq, hcast_partial, show besselI_series n ((q : ℝ)) =
        ∑' k : ℕ, ((q : ℝ) / 2) ^ (n + 2 * k) / ((k.factorial : ℝ) * ((n + k).factorial : ℝ)) from rfl]
    exact sum_le_tsum _ (fun i _ => hg_nonneg i) hTsum
  · rw [kp_hi_eq]
    have hsplit : besselI_series n ((q : ℝ)) =
        (∑ k ∈ Finset.range 41,
          ((q : ℝ) / 2) ^ (n + 2 * k) / ((k.factorial : ℝ) * ((n + k).factorial : ℝ)))
          + ∑' i : ℕ, ((q : ℝ) / 2) ^ (n + 2 * (i + 41))
              / (((i + 41).factorial : ℝ) * ((n + (i + 41)).factorial : ℝ)) := by
      change ∑' k : ℕ, _ = _
      exact (sum_add_tsum_nat_add 41 hTsum).symm
    have htail_le : ∑' i : ℕ, ((q : ℝ) / 2) ^ (n + 2 * (i + 41))
            / (((i + 41).factorial : ℝ) * ((n + (i + 41)).factorial : ℝ))
          ≤ ((besselIn_error n q 40 : ℚ) : ℝ) := by
      rw [hcast_error]
      simpa using besseln_tail_kp n (q : ℝ) 40 hqR.le (by exact_mod_cast hr1Q)
    calc besselI_series n ((q : ℝ))
        = _ + _ := hsplit
      _ ≤ _ + ((besselIn_error n q 40 : ℚ) : ℝ) := add_le_add_left htail_le _
      _ = ((besselIn_partial n q 40 : ℚ) : ℝ) + ((besselIn_error n q 40 : ℚ) : ℝ) := by
            rw [hcast_partial]
      _ = _ := by rw [Rat.cast_add]

-- err_n ≤ err_0 (monotone in Bessel order)
private lemma kp_err_le_I0 (n : ℕ) :
    besselIn_error n (β_kp_rat / 3) 40 ≤ besselI0_error (β_kp_rat / 3) 40 := by
  set x : ℚ := β_kp_rat / 3
  have hF1 : (0 : ℚ) < ((40 + 1).factorial : ℚ) := by positivity
  have hDr0 : (0 : ℚ) < 1 - (x / 2) ^ 2 / ((40 : ℕ) + 2 : ℚ) := by
    norm_num [β_kp_rat]
  have hDle : 1 - (x / 2) ^ 2 / ((40 : ℕ) + 2 : ℚ)
      ≤ 1 - (x / 2) ^ 2 / ((n : ℚ) + (40 : ℕ) + 2) := by
    apply sub_le_sub_left
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by push_cast; linarith)
  have hpow : (x / 2) ^ (n + 2 * (40 + 1)) ≤ (x / 2) ^ (2 * 40 + 2) := by
    rw [show n + 2 * 41 = (2 * 40 + 2) + n from by omega, pow_add]
    calc (x / 2) ^ (2 * 40 + 2) * (x / 2) ^ n
        ≤ (x / 2) ^ (2 * 40 + 2) * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one n kp_q_half_nn kp_q_half_le1) (pow_nonneg kp_q_half_nn _)
      _ = _ := mul_one _
  have hfacN : ((40 + 1).factorial : ℚ) ≤ ((n + (40 + 1)).factorial : ℚ) :=
    by exact_mod_cast Nat.factorial_le (Nat.le_add_left (40 + 1) n)
  unfold besselIn_error besselI0_error
  refine le_trans (div_le_div_of_nonneg_left ?_ hDr0 hDle) ?_
  · exact div_nonneg (pow_nonneg kp_q_half_nn _) (by positivity)
  · exact (div_le_div_right hDr0).mpr
      (div_le_div (pow_nonneg kp_q_half_nn _) hpow (mul_pos hF1 hF1)
        (mul_le_mul_of_nonneg_left hfacN hF1.le))

theorem besselIn_kp_lo_nonneg (n : ℕ) : 0 ≤ (besselIn_kp_interval n).lo := by
  rw [kp_lo_eq]; unfold besselIn_partial
  apply Finset.sum_nonneg; intro k _
  exact div_nonneg (pow_nonneg (div_nonneg kp_q_pos.le (by norm_num)) _) (by positivity)

theorem besselIn_kp_hi_le (n : ℕ) : (besselIn_kp_interval n).hi ≤ 42 := by
  rw [kp_hi_eq]
  have hp : besselIn_partial n (β_kp_rat / 3) 40 ≤ 41 := by
    unfold besselIn_partial
    have hbnd : ∑ k ∈ Finset.range 41,
        (β_kp_rat / 3 / 2) ^ (n + 2 * k) /
          ((k.factorial : ℚ) * ((n + k).factorial : ℚ)) ≤
        ∑ _ ∈ Finset.range 41, (1 : ℚ) := by
      apply Finset.sum_le_sum; intro k _
      rw [div_le_one (by positivity)]
      calc (β_kp_rat / 3 / 2) ^ (n + 2 * k)
          ≤ 1 ^ (n + 2 * k) := pow_le_pow_left kp_q_half_nn kp_q_half_le1 _
        _ = 1 := one_pow _
        _ ≤ ((k.factorial : ℚ) * ((n + k).factorial : ℚ)) :=
            by exact_mod_cast Nat.one_le_iff_ne_zero.mpr
              (Nat.mul_ne_zero (Nat.factorial_ne_zero k) (Nat.factorial_ne_zero _))
    linarith [hbnd, show ∑ _ ∈ Finset.range 41, (1 : ℚ) = 41 from by simp]
  have he : besselIn_error n (β_kp_rat / 3) 40 ≤ 1 :=
    le_trans (kp_err_le_I0 n) (by norm_num [besselI0_error, β_kp_rat, Nat.factorial])
  linarith

/-! ## §7  Toeplitz det interval for β_kp -/

def toeplitzDetInterval_kp (k : ℤ) : RatInterval :=
  detI (fun i j => besselIn_kp_interval (((i : ℤ) - j - k).natAbs))

theorem toeplitz_det_kp_contains (k : ℤ) :
    (toeplitzDetInterval_kp k).contains ((toeplitzReal βR k).det) := by
  apply detI_contains; intro i j
  simp only [toeplitzReal, Matrix.of_apply]
  have : βR / 3 = ((β_kp_rat / 3 : ℚ) : ℝ) := by push_cast; ring
  rw [this]; exact besselIn_kp_contains _

/-! ## §8  Rational constants -/

def finite_kp_hi_sum : ℚ :=
  ∑ i ∈ Finset.range 51, (toeplitzDetInterval_kp ((i : ℤ) - 25)).hi

/-- Tail bound: 2 · 6 · C_exp³ · q²⁴ · (1−q)⁻¹ ≤ 2·162·(729/1331)²⁴·(1331/602) ≈ 3.8e-4 ≤ 1/100.
This is looser than tail_ub for β₀ (which was 1/10²⁰) because q_kp ≈ 0.513 ≫ q₀ ≈ 0.041. -/
def tail_kp_ub : ℚ := 1 / 100

/-! ## §9  natAbs at complement elements and g_kp factoring -/

private lemma natAbs_kp_pos (n : ℕ) : (↑n + 26 : ℤ).natAbs = n + 26 := by
  rw [show (↑n + 26 : ℤ) = ↑(n + 26 : ℕ) from by push_cast; ring]; exact Int.natAbs_ofNat _

private lemma natAbs_kp_neg (n : ℕ) : (-(↑n + 26 : ℤ)).natAbs = n + 26 := by
  rw [Int.natAbs_neg]; exact natAbs_kp_pos n

private lemma g_kp_pos_eq (n : ℕ) :
    g_kp (↑n + 26 : ℤ) = 6 * C_exp_kp ^ 3 * q_kp ^ 24 * q_kp ^ n := by
  unfold g_kp; rw [natAbs_kp_pos, show n + 26 - 2 = n + 24 from by omega, pow_add]; ring

private lemma g_kp_neg_eq (n : ℕ) :
    g_kp (-(↑n + 26) : ℤ) = 6 * C_exp_kp ^ 3 * q_kp ^ 24 * q_kp ^ n := by
  unfold g_kp; rw [natAbs_kp_neg, show n + 26 - 2 = n + 24 from by omega, pow_add]; ring

/-! ## §10  ℕ-bijections for complement halves -/

private def posEquiv_kp : ℕ ≃ {k : ℤ | k ≥ 26} where
  toFun n := ⟨↑n + 26, by simp only [Set.mem_setOf_eq]; omega⟩
  invFun k := (k.val - 26).toNat
  left_inv n := by simp only; omega
  right_inv := fun ⟨k, hk⟩ => by
    simp only [Set.mem_setOf_eq] at hk; apply Subtype.ext; simp only; omega

private def negEquiv_kp : ℕ ≃ {k : ℤ | k ≤ -26} where
  toFun n := ⟨-(↑n + 26), by simp only [Set.mem_setOf_eq]; omega⟩
  invFun k := (-k.val - 26).toNat
  left_inv n := by simp only; omega
  right_inv := fun ⟨k, hk⟩ => by
    simp only [Set.mem_setOf_eq] at hk; apply Subtype.ext; simp only; omega

private lemma compl_S26kp_eq :
    (↑S26kp : Set ℤ)ᶜ = {k : ℤ | k ≥ 26} ∪ {k : ℤ | k ≤ -26} := by
  ext k; simp only [Set.mem_compl_iff, Finset.mem_coe, S26kp, Finset.mem_Icc,
    Set.mem_union, Set.mem_setOf_eq, not_and_or, not_le]; omega

/-! ## §11  Tail bound ∑'_{compl} g_kp ≤ 1/100 -/

/-- Bound: 2 · 6 · C³ · q²⁴ / (1−q) ≤ 2 · 162 · (729/1331)²⁴ · (1331/602) ≤ 1/100. -/
private lemma compl_g_kp_tsum_le :
    ∑' k : ↥((↑S26kp : Set ℤ))ᶜ, g_kp (k : ℤ) ≤ (tail_kp_ub : ℝ) := by
  rw [compl_S26kp_eq]
  have hdisj : Disjoint {k : ℤ | k ≥ 26} {k : ℤ | k ≤ -26} :=
    Set.disjoint_left.mpr fun k h1 h2 => by
      simp only [Set.mem_setOf_eq] at h1 h2; omega
  rw [tsum_union_disjoint hdisj (g_kp_summable.subtype _) (g_kp_summable.subtype _)]
  have hpos_idx : ∑' k : {k : ℤ | k ≥ 26}, g_kp k.val = ∑' n : ℕ, g_kp (↑n + 26 : ℤ) :=
    ((Equiv.tsum_eq posEquiv_kp (fun k : {k : ℤ | k ≥ 26} => g_kp k.val)).symm).trans
      (by simp only [posEquiv_kp, Equiv.coe_fn_mk])
  have hneg_idx : ∑' k : {k : ℤ | k ≤ -26}, g_kp k.val = ∑' n : ℕ, g_kp (-(↑n + 26) : ℤ) :=
    ((Equiv.tsum_eq negEquiv_kp (fun k : {k : ℤ | k ≤ -26} => g_kp k.val)).symm).trans
      (by simp only [negEquiv_kp, Equiv.coe_fn_mk])
  rw [hpos_idx, hneg_idx]
  simp_rw [g_kp_pos_eq, g_kp_neg_eq]
  have hgeo : ∑' n : ℕ, 6 * C_exp_kp ^ 3 * q_kp ^ 24 * q_kp ^ n =
      6 * C_exp_kp ^ 3 * q_kp ^ 24 * (1 - q_kp)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one q_kp_nonneg q_kp_lt_one]
  rw [hgeo, hgeo]
  have hC3 : C_exp_kp ^ 3 ≤ (3 : ℝ) ^ 3 :=
    pow_le_pow_left C_exp_kp_nonneg C_exp_kp_lt_three.le 3
  have hq24 : q_kp ^ 24 ≤ (729 / 1331 : ℝ) ^ 24 :=
    pow_le_pow_left q_kp_nonneg q_kp_lt_729_1331.le 24
  have hq_pos : (0 : ℝ) < 1 - q_kp := by linarith [q_kp_lt_one]
  have h_lhs : 6 * C_exp_kp ^ 3 * q_kp ^ 24 ≤ 6 * (3 : ℝ) ^ 3 * (729 / 1331 : ℝ) ^ 24 :=
    by nlinarith [mul_le_mul hC3 hq24 (pow_nonneg q_kp_nonneg 24) (by positivity : (0:ℝ) ≤ (3:ℝ)^3)]
  have h_each : 6 * C_exp_kp ^ 3 * q_kp ^ 24 * (1 - q_kp)⁻¹ ≤
      162 * (729 / 1331 : ℝ) ^ 24 * (1331 / 602) :=
    calc 6 * C_exp_kp ^ 3 * q_kp ^ 24 * (1 - q_kp)⁻¹
        ≤ 6 * (3 : ℝ) ^ 3 * (729 / 1331 : ℝ) ^ 24 * (1331 / 602) :=
            mul_le_mul h_lhs inv_one_sub_q_kp_le (inv_nonneg.mpr hq_pos.le) (by positivity)
      _ = 162 * (729 / 1331 : ℝ) ^ 24 * (1331 / 602) := by norm_num
  simp only [tail_kp_ub]
  linarith [show 2 * (162 * (729 / 1331 : ℝ) ^ 24 * (1331 / 602)) ≤ 1 / 100 from by
    norm_num [show (729 : ℝ) ^ 24 / (1331 : ℝ) ^ 24 = (729 ^ 24 : ℚ) / (1331 ^ 24 : ℚ) from
      by push_cast; rfl]]

/-! ## §12  Tail det bound, tsum split, finite sum bound -/

private lemma tail_kp_le_ub :
    ∑' k : ↥((↑S26kp : Set ℤ))ᶜ, (toeplitzReal βR (k : ℤ)).det ≤ (tail_kp_ub : ℝ) :=
  le_trans
    (tsum_le_tsum (fun k => le_trans (le_abs_self _) (det_abs_kp_le k.val))
      (summable_toeplitz_det_kp.subtype _) (g_kp_summable.subtype _))
    compl_g_kp_tsum_le

private lemma tsum_kp_det_split :
    ∑' k : ℤ, (toeplitzReal βR k).det =
    ∑ k ∈ S26kp, (toeplitzReal βR k).det +
    ∑' k : ↥((↑S26kp : Set ℤ))ᶜ, (toeplitzReal βR (k : ℤ)).det :=
  (sum_add_tsum_compl (s := S26kp) summable_toeplitz_det_kp).symm

private lemma finite_kp_sum_le :
    ∑ i ∈ Finset.range 51, (toeplitzReal βR ((i : ℤ) - 25)).det ≤
    (finite_kp_hi_sum : ℝ) := by
  apply le_trans (Finset.sum_le_sum (fun i _ => (toeplitz_det_kp_contains ((i : ℤ) - 25)).2))
  simp only [finite_kp_hi_sum]; push_cast; rfl

/-! ## §13  Part (b): ∑' det ≤ finite_kp_hi_sum + tail_kp_ub -/

theorem kp_tsum_det_le :
    ∑' k : ℤ, (toeplitzReal βR k).det ≤ (↑finite_kp_hi_sum + ↑tail_kp_ub : ℝ) := by
  rw [tsum_kp_det_split]
  have h_finite : ∑ k ∈ S26kp, (toeplitzReal βR k).det ≤ (↑finite_kp_hi_sum : ℝ) := by
    have h_reindex : ∑ k ∈ S26kp, (toeplitzReal βR k).det =
        ∑ i ∈ Finset.range 51, (toeplitzReal βR ((i : ℤ) - 25)).det := by
      apply Finset.sum_nbij (fun i => (i : ℤ) - 25)
      · intro i hi; simp only [S26kp, Finset.mem_Icc]; simp only [Finset.mem_range] at hi; omega
      · intro i₁ _ i₂ _ h; omega
      · intro k hk; simp only [S26kp, Finset.mem_Icc] at hk
        exact ⟨(k + 25).toNat, by simp only [Finset.mem_range]; omega, by omega⟩
      · intro i _; rfl
    rw [h_reindex]; exact finite_kp_sum_le
  linarith [tail_kp_le_ub]

/-! ## §14  Part (c): pure ℚ inequality -/

/-- P₂₈(β_kp) · (finite_kp_hi_sum + tail_kp_ub) < 1/56 — pure ℚ.
    Margin: 1/56 − P₂₈·(F+T) ≈ 1.5e-3.
    Denominators ≈ 10^460 (vs β₀ case ≈ 10^946) → `decide` faster. -/
set_option maxHeartbeats 400000000 in
theorem kp_part_c :
    exp_neg_partial β_kp_rat 28 * (finite_kp_hi_sum + tail_kp_ub) < 1 / 56 := by
  norm_num [exp_neg_partial, β_kp_rat, finite_kp_hi_sum, tail_kp_ub,
            toeplitzDetInterval_kp, detI, besselIn_kp_interval, besselIn_interval,
            ofRat, RatInterval.hi, RatInterval.lo,
            Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

/-! ## §15  Main theorem -/

/-- **w1_weyl_series(β_kp) < 1/56** — classical trio only, 0 gaps.
    β_kp = 30029/6250 = 4.80464 = beta0_kp_star in KP_Closure.lean. -/
theorem w1_kp_lt : w1_weyl_series βR < 1 / 56 := by
  have hQ : (exp_neg_partial β_kp_rat 28 : ℝ) * (↑finite_kp_hi_sum + ↑tail_kp_ub) < 1 / 56 :=
    by exact_mod_cast kp_part_c
  have hexp : Real.exp (-βR) ≤ ((exp_neg_partial β_kp_rat 28 : ℚ) : ℝ) := exp_kp_upper
  have hdet_le := kp_tsum_det_le
  unfold w1_weyl_series
  -- Use case split: ∑' det ≥ 0 or ∑' det < 0
  rcases le_or_lt 0 (∑' k : ℤ, (toeplitzReal βR k).det) with hnn | hneg
  · -- Case: ∑' det ≥ 0 → F+T ≥ 0 → both factors well-ordered
    have hFT_nn : (0 : ℝ) ≤ ↑finite_kp_hi_sum + ↑tail_kp_ub :=
      le_trans hnn hdet_le
    calc Real.exp (-βR) * ∑' k : ℤ, (toeplitzReal βR k).det
        ≤ Real.exp (-βR) * (↑finite_kp_hi_sum + ↑tail_kp_ub) :=
            mul_le_mul_of_nonneg_left hdet_le (Real.exp_pos _).le
      _ ≤ (exp_neg_partial β_kp_rat 28 : ℝ) * (↑finite_kp_hi_sum + ↑tail_kp_ub) :=
            mul_le_mul_of_nonneg_right hexp hFT_nn
      _ < 1 / 56 := hQ
  · -- Case: ∑' det < 0 → exp(-β)·(∑' det) < 0 < 1/56
    have : Real.exp (-βR) * ∑' k : ℤ, (toeplitzReal βR k).det < 0 :=
      mul_neg_of_pos_of_neg (Real.exp_pos _) hneg
    linarith

/-- Connection: beta0_kp_star = 4.80464 = β_kp_rat as a real. -/
theorem beta0_kp_eq_rat : (4.80464 : ℝ) = βR := by norm_num [β_kp_rat]

end TheoremaAureum.Towers.YM.KPW1Proof

-- #print axioms TheoremaAureum.Towers.YM.KPW1Proof.w1_kp_lt
-- Expected: [propext, Classical.choice, Quot.sound]
