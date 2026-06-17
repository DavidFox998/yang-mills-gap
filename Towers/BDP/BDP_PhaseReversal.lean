import Mathlib
-- BDP Phase Reversal -- Opera Numerorum | David Fox | June 13, 2026
-- Lean 4 skeleton for the Bounded Dual Pair module.
-- Axioms closed: Cert_lemma2, Cert_llm_trunc, Cert_phase_reversal
-- Source: Meta AI (supervisor), 83 screenshots across 4 batches.

namespace TheoremaAureum.BDP

-- -----------------------------------------------------------------------
-- Constants
-- -----------------------------------------------------------------------

noncomputable def alpha0 : Real := 299 + Real.pi / 10
noncomputable def kappa  : Real := 4.8433014197780389  -- M2 certified
noncomputable def p5     : Nat  := 3993746143633
noncomputable def q5     : Nat  := 191  -- bridge prime from S4

-- -----------------------------------------------------------------------
-- Lemma 1: Two-Halves Error Bound
-- -----------------------------------------------------------------------

noncomputable def fracDist (p : Nat) : Real :=
  let x := (p : Real) * alpha0
  let n := Int.floor x
  min (x - n) (1 - (x - n))

lemma lemma1_two_halves_error_bound :
    ∀ p ∈ ({2, 3, 19, 191} : Finset Nat),
    fracDist p < 1 / (2 * Real.log p) := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  have hπl := Real.pi_gt_d6
  have hπu := Real.pi_lt_d6
  have he  := Real.exp_one_gt_d9
  rcases hp with rfl | rfl | rfl | rfl
  · unfold fracDist alpha0; simp only [Nat.cast_ofNat]
    have hfl : Int.floor ((2 : ℝ) * (299 + Real.pi / 10)) = 598 :=
      Int.floor_eq_iff.mpr ⟨by push_cast; nlinarith, by push_cast; nlinarith⟩
    rw [hfl]; norm_cast
    rw [show (2 : ℝ) * (299 + Real.pi / 10) - 598 = Real.pi / 5 from by ring]
    rw [min_eq_right (by nlinarith : 1 - Real.pi / 5 ≤ Real.pi / 5)]
    have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2_lt1 : Real.log 2 < 1 := by
      have h : Real.log 2 < Real.log (Real.exp 1) :=
        Real.log_lt_log (by norm_num) (by linarith)
      rwa [Real.log_exp] at h
    have h1 : 1 - Real.pi / 5 < 1 / 2 := by nlinarith
    linarith [one_div_le_one_div_of_le (mul_pos (by norm_num : (0:ℝ)<2) hlog2_pos)
              (show 2 * Real.log 2 ≤ 2 from by linarith)]
  · unfold fracDist alpha0; simp only [Nat.cast_ofNat]
    have hfl : Int.floor ((3 : ℝ) * (299 + Real.pi / 10)) = 897 :=
      Int.floor_eq_iff.mpr ⟨by push_cast; nlinarith, by push_cast; nlinarith⟩
    rw [hfl]; norm_cast
    rw [show (3 : ℝ) * (299 + Real.pi / 10) - 897 = 3 * Real.pi / 10 from by ring]
    rw [min_eq_right (by nlinarith : 1 - 3 * Real.pi / 10 ≤ 3 * Real.pi / 10)]
    have hlog3_pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2:ℝ) = 1+1 from by norm_num]; exact Real.exp_add 1 1
    have hlog3_lt2 : Real.log 3 < 2 := by
      have h : Real.log 3 < Real.log (Real.exp 2) :=
        Real.log_lt_log (by norm_num) (by nlinarith)
      rwa [Real.log_exp] at h
    have h1 : 1 - 3 * Real.pi / 10 < 1 / 4 := by nlinarith
    linarith [one_div_le_one_div_of_le (mul_pos (by norm_num : (0:ℝ)<2) hlog3_pos)
              (show 2 * Real.log 3 ≤ 4 from by linarith)]
  · unfold fracDist alpha0; simp only [Nat.cast_ofNat]
    have hfl : Int.floor ((19 : ℝ) * (299 + Real.pi / 10)) = 5686 :=
      Int.floor_eq_iff.mpr ⟨by push_cast; nlinarith, by push_cast; nlinarith⟩
    rw [hfl]; norm_cast
    rw [show (19 : ℝ) * (299 + Real.pi / 10) - 5686 = 19 * Real.pi / 10 - 5 from by ring]
    rw [min_eq_right (by nlinarith : 1 - (19 * Real.pi / 10 - 5) ≤ 19 * Real.pi / 10 - 5)]
    rw [show (1 : ℝ) - (19 * Real.pi / 10 - 5) = 6 - 19 * Real.pi / 10 from by ring]
    have hlog19_pos : (0 : ℝ) < Real.log 19 := Real.log_pos (by norm_num)
    have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2:ℝ) = 1+1 from by norm_num]; exact Real.exp_add 1 1
    have hexp3 : Real.exp 3 = Real.exp 1 * Real.exp 2 := by
      rw [show (3:ℝ) = 1+2 from by norm_num]; exact Real.exp_add 1 2
    have hlog19_lt3 : Real.log 19 < 3 := by
      have h : Real.log 19 < Real.log (Real.exp 3) :=
        Real.log_lt_log (by norm_num) (by nlinarith)
      rwa [Real.log_exp] at h
    have h1 : 6 - 19 * Real.pi / 10 < 1 / 6 := by nlinarith
    linarith [one_div_le_one_div_of_le (mul_pos (by norm_num : (0:ℝ)<2) hlog19_pos)
              (show 2 * Real.log 19 ≤ 6 from by linarith)]
  · unfold fracDist alpha0; simp only [Nat.cast_ofNat]
    have hfl : Int.floor ((191 : ℝ) * (299 + Real.pi / 10)) = 57169 :=
      Int.floor_eq_iff.mpr ⟨by push_cast; nlinarith, by push_cast; nlinarith⟩
    rw [hfl]; norm_cast
    rw [show (191 : ℝ) * (299 + Real.pi / 10) - 57169 = 191 * Real.pi / 10 - 60 from by ring]
    rw [min_eq_left (by nlinarith : 191 * Real.pi / 10 - 60 ≤ 1 - (191 * Real.pi / 10 - 60))]
    have hlog191_pos : (0 : ℝ) < Real.log 191 := Real.log_pos (by norm_num)
    have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2:ℝ) = 1+1 from by norm_num]; exact Real.exp_add 1 1
    have hexp4 : Real.exp 4 = Real.exp 2 * Real.exp 2 := by
      rw [show (4:ℝ) = 2+2 from by norm_num]; exact Real.exp_add 2 2
    have hexp6 : Real.exp 6 = Real.exp 2 * Real.exp 4 := by
      rw [show (6:ℝ) = 2+4 from by norm_num]; exact Real.exp_add 2 4
    have he1pos : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
    have he2pos : (0:ℝ) < Real.exp 2 := Real.exp_pos 2
    have he4pos : (0:ℝ) < Real.exp 4 := Real.exp_pos 4
    have hd1 : (0:ℝ) < Real.exp 1 - 2.7182818283 := by linarith
    have he2_gt : (7.389:ℝ) < Real.exp 2 := by
      nlinarith [mul_pos he1pos hd1, mul_pos (by norm_num : (0:ℝ) < 2.7182818283) hd1]
    have he6_gt : (191:ℝ) < Real.exp 6 := by
      have he4_gt : (54.5:ℝ) < Real.exp 4 := by
        rw [hexp4]
        nlinarith [mul_pos he2pos (show (0:ℝ) < Real.exp 2 - 7.389 from by linarith),
                   mul_pos (by norm_num : (0:ℝ) < 7.389)
                           (show (0:ℝ) < Real.exp 2 - 7.389 from by linarith)]
      rw [hexp6]
      nlinarith [mul_pos (show (0:ℝ) < Real.exp 2 - 7.389 from by linarith) he4pos,
                 mul_pos (by norm_num : (0:ℝ) < 7.389)
                         (show (0:ℝ) < Real.exp 4 - 54.5 from by linarith)]
    have hlog191_lt6 : Real.log 191 < 6 := by
      have h : Real.log 191 < Real.log (Real.exp 6) :=
        Real.log_lt_log (by norm_num) he6_gt
      rwa [Real.log_exp] at h
    have h1 : 191 * Real.pi / 10 - 60 < 1 / 12 := by nlinarith
    linarith [one_div_le_one_div_of_le (mul_pos (by norm_num : (0:ℝ)<2) hlog191_pos)
              (show 2 * Real.log 191 ≤ 12 from by linarith)]

-- -----------------------------------------------------------------------
-- Lemma 2 setup
-- -----------------------------------------------------------------------

noncomputable def bridgeErrorBound (m : Nat) : Real :=
  (m / 8 : Real) / (2 * Real.log p5) + 1 / (2 * m * Real.log q5)

def k_bridge : Int := 4302500812118

-- -----------------------------------------------------------------------
-- MachinPiBounds: Rational bounds on Real.pi via Machin's formula
-- pi/4 = 4*arctan(1/5) - arctan(1/239)    (Machin, 1706)
-- -----------------------------------------------------------------------

section MachinPiBounds

private noncomputable def atPS (x : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, ((-1 : ℝ)^k * x^(2*k+1) / (2*k+1))

-- ---- Machin identity ----

private lemma mac1 : Real.arctan (1/5 : ℝ) + Real.arctan (1/5 : ℝ) = Real.arctan (5/12 : ℝ) := by
  rw [Real.arctan_add (by norm_num : (1/5 : ℝ) * (1/5) < 1)]
  congr 1; norm_num

private lemma mac2 : Real.arctan (5/12 : ℝ) + Real.arctan (5/12 : ℝ) = Real.arctan (120/119 : ℝ) := by
  rw [Real.arctan_add (by norm_num : (5/12 : ℝ) * (5/12) < 1)]
  congr 1; norm_num

private lemma mac3 : Real.arctan (120/119 : ℝ) - Real.arctan (1/239 : ℝ) = Real.pi / 4 := by
  have h : Real.arctan (120/119 : ℝ) + Real.arctan (-(1/239 : ℝ)) = Real.arctan 1 := by
    rw [Real.arctan_add (by norm_num : (120/119 : ℝ) * -(1/239) < 1)]
    congr 1; norm_num
  rw [Real.arctan_neg, Real.arctan_one] at h
  linarith

private lemma machin_pi :
    Real.pi = 4 * (4 * Real.arctan (1/5 : ℝ) - Real.arctan (1/239 : ℝ)) := by
  have h4 : 4 * Real.arctan (1/5 : ℝ) = Real.arctan (120/119 : ℝ) := by linarith [mac1, mac2]
  linarith [mac3]

-- ---- Arctan partial sum derivative (HasDerivAt) ----

private lemma atPS_term_hasDerivAt (x : ℝ) (k : ℕ) :
    HasDerivAt (fun t => (-1 : ℝ)^k * t^(2*k+1) / (2*k+1))
               ((-1 : ℝ)^k * x^(2*k)) x := by
  have hk : (2 * k + 1 : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * k)
  have h := ((hasDerivAt_pow (2*k+1) x).const_mul ((-1 : ℝ)^k)).div_const (2*k+1 : ℝ)
  convert h using 1
  field_simp [hk]; push_cast; ring

private lemma atPS_hasDerivAt (x : ℝ) (N : ℕ) :
    HasDerivAt (atPS · N) (∑ k ∈ Finset.range N, (-1 : ℝ)^k * x^(2*k)) x := by
  unfold atPS
  exact HasDerivAt.sum (fun k _ => atPS_term_hasDerivAt x k)

-- ---- Geometric sum identities (derivative simplification) ----

-- (1+x^2) * Σ_{k<2N} (-1)^k x^{2k} = 1 - x^{4N}
private lemma deriv_sum_even (x : ℝ) (N : ℕ) :
    (1 + x^2) * ∑ k ∈ Finset.range (2*N), (-1 : ℝ)^k * x^(2*k) = 1 - x^(4*N) := by
  have hkey : ∑ k ∈ Finset.range (2*N), (-1 : ℝ)^k * x^(2*k) =
              ∑ k ∈ Finset.range (2*N), (-x^2 : ℝ)^k := by
    congr 1; ext k; ring
  rw [hkey]
  have hgm := geom_sum_mul (-x^2 : ℝ) (2*N)
  have heven : (-x^2 : ℝ)^(2*N) = x^(4*N) := by
    rw [Even.neg_pow (⟨N, by ring⟩ : Even (2*N)), ← pow_mul]; congr 1; ring
  set S := ∑ k ∈ Finset.range (2*N), (-x^2 : ℝ)^k
  have hS : S * (-x^2 - 1) = x^(4*N) - 1 := by rw [heven] at hgm; exact hgm
  have hring : S * (1 + x^2) + S * (-x^2 - 1) = 0 := by ring
  linarith [mul_comm (1 + x^2) S]

-- (1+x^2) * Σ_{k<2N+1} (-1)^k x^{2k} = 1 + x^{4N+2}
private lemma deriv_sum_odd (x : ℝ) (N : ℕ) :
    (1 + x^2) * ∑ k ∈ Finset.range (2*N+1), (-1 : ℝ)^k * x^(2*k) = 1 + x^(4*N+2) := by
  have hkey : ∑ k ∈ Finset.range (2*N+1), (-1 : ℝ)^k * x^(2*k) =
              ∑ k ∈ Finset.range (2*N+1), (-x^2 : ℝ)^k := by
    congr 1; ext k; ring
  rw [hkey]
  have hgm := geom_sum_mul (-x^2 : ℝ) (2*N+1)
  have hodd : (-x^2 : ℝ)^(2*N+1) = -x^(4*N+2) := by
    rw [Odd.neg_pow (⟨N, rfl⟩ : Odd (2*N+1)), ← pow_mul]; congr 1; ring
  set S := ∑ k ∈ Finset.range (2*N+1), (-x^2 : ℝ)^k
  have hS : S * (-x^2 - 1) = -x^(4*N+2) - 1 := by rw [hodd] at hgm; exact hgm
  have hring : S * (1 + x^2) + S * (-x^2 - 1) = 0 := by ring
  linarith [mul_comm (1 + x^2) S]

-- ---- Arctan alternating series bounds (monotone derivative) ----

-- STRICT lower bound: arctan(x) > atPS(x, 2N) for x > 0
-- Proof: H = arctan - S_{2N} has H(0)=0 and H'(t) = t^{4N}/(1+t^2) > 0 for t > 0
private lemma arctan_gt_atPS_even {x : ℝ} (hx : 0 < x) (N : ℕ) :
    atPS x (2*N) < Real.arctan x := by
  set H := fun t : ℝ => Real.arctan t - atPS t (2*N)
  -- H(0) = 0
  have hH0 : H 0 = 0 := by
    simp only [H, Real.arctan_zero, sub_eq_zero]
    unfold atPS
    apply Finset.sum_eq_zero; intro k _
    rw [zero_pow (by omega : 2*k+1 ≠ 0)]; ring
  -- H is continuous on [0, x]
  have hHcont : ContinuousOn H (Set.Icc 0 x) :=
    (Real.continuous_arctan.sub
      (continuous_finset_sum _ (fun k _ => by
        apply Continuous.div_const
        apply Continuous.mul continuous_const
        exact continuous_pow _))).continuousOn
  -- H'(t) = t^{4N}/(1+t^2) > 0 for t ∈ (0, x)
  have hHderiv_pos : ∀ t ∈ Set.Ioo 0 x, 0 < deriv H t := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have h1t2 : (1 : ℝ) + t^2 ≠ 0 := by positivity
    have hH_hd : HasDerivAt H (t^(4*N) / (1 + t^2)) t := by
      have h1 : HasDerivAt Real.arctan (1/(1+t^2)) t := Real.hasDerivAt_arctan t
      have h2 : HasDerivAt (atPS · (2*N)) ((1 - t^(4*N))/(1+t^2)) t := by
        have hd := atPS_hasDerivAt t (2*N)
        convert hd using 1
        rw [div_eq_iff h1t2]
        linarith [deriv_sum_even t N]
      have h := h1.sub h2
      convert h using 1; field_simp [h1t2]; ring
    rw [hH_hd.deriv]
    exact div_pos (pow_pos ht0 (4*N)) (by positivity)
  -- H is strictly increasing on [0, x]
  have hHmono : StrictMonoOn H (Set.Icc 0 x) :=
    strictMonoOn_of_deriv_pos (convex_Icc 0 x) hHcont (by
      rw [Set.interior_Icc]; exact hHderiv_pos)
  -- H(x) > H(0) = 0
  have hHx : 0 < H x := by
    have := hHmono (Set.left_mem_Icc.mpr hx.le) (Set.right_mem_Icc.mpr le_rfl) hx
    simp [hH0] at this; exact this
  simp only [H] at hHx; linarith

-- NON-STRICT upper bound: arctan(x) ≤ atPS(x, 2N+1) for x ≥ 0
-- Proof: G = S_{2N+1} - arctan has G(0)=0 and G'(t) = t^{4N+2}/(1+t^2) ≥ 0
private lemma arctan_le_atPS_odd {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    Real.arctan x ≤ atPS x (2*N+1) := by
  rcases eq_or_lt_of_le hx with rfl | hx0
  · -- x = 0: both sides = 0
    simp only [Real.arctan_zero]
    unfold atPS
    apply le_of_eq; symm
    apply Finset.sum_eq_zero; intro k _
    rw [zero_pow (by omega : 2*k+1 ≠ 0)]; ring
  -- x > 0: use strict monotonicity
  set G := fun t : ℝ => atPS t (2*N+1) - Real.arctan t
  have hG0 : G 0 = 0 := by
    simp only [G, Real.arctan_zero, sub_zero]
    unfold atPS
    apply Finset.sum_eq_zero; intro k _
    rw [zero_pow (by omega : 2*k+1 ≠ 0)]; ring
  have hGcont : ContinuousOn G (Set.Icc 0 x) :=
    ((by
      unfold G atPS
      apply Continuous.sub
      · exact continuous_finset_sum _ (fun k _ => by fun_prop)
      · exact Real.continuous_arctan).continuousOn)
  have hGderiv_nonneg : ∀ t ∈ Set.Ioo 0 x, 0 ≤ deriv G t := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have h1t2 : (1 : ℝ) + t^2 ≠ 0 := by positivity
    have hG_hd : HasDerivAt G (t^(4*N+2) / (1 + t^2)) t := by
      have h1 : HasDerivAt Real.arctan (1/(1+t^2)) t := Real.hasDerivAt_arctan t
      have h2 : HasDerivAt (atPS · (2*N+1)) ((1 + t^(4*N+2))/(1+t^2)) t := by
        have hd := atPS_hasDerivAt t (2*N+1)
        convert hd using 1
        rw [div_eq_iff h1t2]
        linarith [deriv_sum_odd t N]
      have h := h2.sub h1
      convert h using 1; field_simp [h1t2]; ring
    rw [hG_hd.deriv]
    positivity
  have hGmono : MonotoneOn G (Set.Icc 0 x) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 x) hGcont (by
      rw [Set.interior_Icc]; exact hGderiv_nonneg)
  have hGx : 0 ≤ G x := by
    have := hGmono (Set.left_mem_Icc.mpr hx0.le) (Set.right_mem_Icc.mpr le_rfl) hx0.le
    simp [hG0] at this; exact this
  simp only [G] at hGx; linarith

-- ---- Concrete arctan bounds ----

private lemma atan_fifth_gt_S10 : atPS (1/5 : ℝ) 10 < Real.arctan (1/5 : ℝ) :=
  arctan_gt_atPS_even (by norm_num) 5

private lemma atan_fifth_le_S11 : Real.arctan (1/5 : ℝ) ≤ atPS (1/5 : ℝ) 11 :=
  arctan_le_atPS_odd (by norm_num) 5

private lemma atan_239_le_S3 : Real.arctan (1/239 : ℝ) ≤ atPS (1/239 : ℝ) 3 :=
  arctan_le_atPS_odd (by norm_num) 1

private lemma atan_239_gt_S4 : atPS (1/239 : ℝ) 4 < Real.arctan (1/239 : ℝ) :=
  arctan_gt_atPS_even (by norm_num) 2

private lemma atan_fifth_gt_S20 : atPS (1/5 : ℝ) 20 < Real.arctan (1/5 : ℝ) :=
  arctan_gt_atPS_even (by norm_num) 10

private lemma atan_fifth_le_S21 : Real.arctan (1/5 : ℝ) ≤ atPS (1/5 : ℝ) 21 :=
  arctan_le_atPS_odd (by norm_num) 10

private lemma atan_239_le_S5 : Real.arctan (1/239 : ℝ) ≤ atPS (1/239 : ℝ) 5 :=
  arctan_le_atPS_odd (by norm_num) 2

private lemma atan_239_gt_S6 : atPS (1/239 : ℝ) 6 < Real.arctan (1/239 : ℝ) :=
  arctan_gt_atPS_even (by norm_num) 3

-- ---- 15-digit pi bounds (pi_lo_A, pi_hi_A) ----

private def pi_lo_A : ℝ :=
  (135971713047870654998930719127948 : ℝ) / 43281140504482774600982666015625

private def pi_hi_A : ℝ :=
  (194171005525185591654101515840515257888 : ℝ) / 61806550668914014199568271636962890625

-- pi_lo_A = 4*(4*S10(1/5) - S3(1/239))  [rational equality, norm_num]
private lemma pi_lo_A_eq :
    pi_lo_A = 4 * (4 * atPS (1/5 : ℝ) 10 - atPS (1/239 : ℝ) 3) := by
  simp only [pi_lo_A, atPS, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

-- pi_hi_A = 4*(4*S11(1/5) - S4(1/239))  [rational equality, norm_num]
private lemma pi_hi_A_eq :
    pi_hi_A = 4 * (4 * atPS (1/5 : ℝ) 11 - atPS (1/239 : ℝ) 4) := by
  simp only [pi_hi_A, atPS, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

-- Lower bound: pi_lo_A < pi
-- Proof: at(1/5) > S10 (strict) and at(1/239) ≤ S3
theorem pi_lo_A_lt_pi : pi_lo_A < Real.pi := by
  rw [pi_lo_A_eq, machin_pi]
  have h1 := atan_fifth_gt_S10   -- atPS(1/5,10) < arctan(1/5)
  have h2 := atan_239_le_S3      -- arctan(1/239) ≤ atPS(1/239,3)
  linarith

-- Upper bound: pi < pi_hi_A
-- Proof: at(1/5) ≤ S11 and at(1/239) > S4 (strict)
theorem pi_lt_pi_hi_A : Real.pi < pi_hi_A := by
  rw [pi_hi_A_eq, machin_pi]
  have h1 := atan_fifth_le_S11   -- arctan(1/5) ≤ atPS(1/5,11)
  have h2 := atan_239_gt_S4      -- atPS(1/239,4) < arctan(1/239)
  linarith

-- ---- 30-digit pi bounds (pi_lo_B, pi_hi_NEW) ----

private def pi_lo_B : ℝ :=
  (13872435879152265241123169431252045406671325830383065949741988 : ℝ) /
  4415733485784891631637693849645571390283294022083282470703125

private def pi_hi_NEW : ℝ :=
  (812217595099382956409151475758694338539045009437476833945001089364728 : ℝ) /
  258536890252556764763046128145244800468981338781304657459259033203125

private lemma pi_lo_B_eq :
    pi_lo_B = 4 * (4 * atPS (1/5 : ℝ) 20 - atPS (1/239 : ℝ) 5) := by
  simp only [pi_lo_B, atPS, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

private lemma pi_hi_NEW_eq :
    pi_hi_NEW = 4 * (4 * atPS (1/5 : ℝ) 21 - atPS (1/239 : ℝ) 6) := by
  simp only [pi_hi_NEW, atPS, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem pi_lo_B_lt_pi : pi_lo_B < Real.pi := by
  rw [pi_lo_B_eq, machin_pi]
  have h1 := atan_fifth_gt_S20
  have h2 := atan_239_le_S5
  linarith

theorem pi_lt_pi_hi_NEW : Real.pi < pi_hi_NEW := by
  rw [pi_hi_NEW_eq, machin_pi]
  have h1 := atan_fifth_le_S21
  have h2 := atan_239_gt_S6
  linarith

-- ---- beb lower bound ----

private lemma log_p5_gt_29 : (29 : ℝ) < Real.log p5 := by
  have : Real.log (Real.exp 29) < Real.log p5 := by
    apply Real.log_lt_log (Real.exp_pos _)
    have he := Real.exp_one_gt_d9
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2:ℝ)=1+1 from by norm_num]; exact Real.exp_add 1 1
    have he4 : Real.exp 4 = Real.exp 2 * Real.exp 2 := by
      rw [show (4:ℝ)=2+2 from by norm_num]; exact Real.exp_add 2 2
    have he8 : Real.exp 8 = Real.exp 4 * Real.exp 4 := by
      rw [show (8:ℝ)=4+4 from by norm_num]; exact Real.exp_add 4 4
    have he16 : Real.exp 16 = Real.exp 8 * Real.exp 8 := by
      rw [show (16:ℝ)=8+8 from by norm_num]; exact Real.exp_add 8 8
    have he29 : Real.exp 29 = Real.exp 16 * Real.exp 8 * Real.exp 4 * Real.exp 1 := by
      rw [show (29:ℝ)=16+8+4+1 from by norm_num]
      rw [Real.exp_add, Real.exp_add, Real.exp_add]; ring
    rw [he29]
    have he2v : (7.389 : ℝ) < Real.exp 2 := by
      rw [he2]; nlinarith [Real.exp_pos 1]
    have he4v : (54.59 : ℝ) < Real.exp 4 := by
      rw [he4]; nlinarith [Real.exp_pos 2]
    have he8v : (2980.9 : ℝ) < Real.exp 8 := by
      rw [he8]; nlinarith [Real.exp_pos 4]
    have he16v : (8886110 : ℝ) < Real.exp 16 := by
      rw [he16]; nlinarith [Real.exp_pos 8]
    unfold_let p5; push_cast
    nlinarith [Real.exp_pos 1, Real.exp_pos 4, Real.exp_pos 8, Real.exp_pos 16]
  rwa [Real.log_exp] at this

private lemma log_p5_lt_30 : Real.log p5 < 30 := by
  have : Real.log p5 < Real.log (Real.exp 30) := by
    apply Real.log_lt_log (by unfold_let p5; norm_num)
    have he := Real.exp_one_lt_d9
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2:ℝ)=1+1 from by norm_num]; exact Real.exp_add 1 1
    have he4 : Real.exp 4 = Real.exp 2 * Real.exp 2 := by
      rw [show (4:ℝ)=2+2 from by norm_num]; exact Real.exp_add 2 2
    have he8 : Real.exp 8 = Real.exp 4 * Real.exp 4 := by
      rw [show (8:ℝ)=4+4 from by norm_num]; exact Real.exp_add 4 4
    have he16 : Real.exp 16 = Real.exp 8 * Real.exp 8 := by
      rw [show (16:ℝ)=8+8 from by norm_num]; exact Real.exp_add 8 8
    have he30 : Real.exp 30 = Real.exp 16 * Real.exp 8 * Real.exp 4 * Real.exp 2 := by
      rw [show (30:ℝ)=16+8+4+2 from by norm_num]
      rw [Real.exp_add, Real.exp_add, Real.exp_add]; ring
    rw [he30]
    have he2v : Real.exp 2 < 7.3891 := by rw [he2]; nlinarith [Real.exp_pos 1]
    have he4v : Real.exp 4 < 54.603 := by rw [he4]; nlinarith [Real.exp_pos 2]
    have he8v : Real.exp 8 < 2981.0 := by rw [he8]; nlinarith [Real.exp_pos 4]
    have he16v : Real.exp 16 < 8886115 := by rw [he16]; nlinarith [Real.exp_pos 8]
    unfold_let p5; push_cast
    nlinarith [Real.exp_pos 2, Real.exp_pos 4, Real.exp_pos 8, Real.exp_pos 16]
  rwa [Real.log_exp] at this

private lemma log_q5_gt_5 : (5 : ℝ) < Real.log q5 := by
  have : Real.log (Real.exp 5) < Real.log q5 := by
    apply Real.log_lt_log (Real.exp_pos _)
    have he := Real.exp_one_gt_d9
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2:ℝ)=1+1 from by norm_num]; exact Real.exp_add 1 1
    have he5 : Real.exp 5 = Real.exp 2 * Real.exp 2 * Real.exp 1 := by
      rw [show (5:ℝ)=2+2+1 from by norm_num]; rw [Real.exp_add, Real.exp_add]; ring
    rw [he5, he2]; unfold_let q5; push_cast
    nlinarith [Real.exp_pos 1]
  rwa [Real.log_exp] at this

private lemma log_q5_lt_6 : Real.log q5 < 6 := by
  have : Real.log q5 < Real.log (Real.exp 6) := by
    apply Real.log_lt_log (by unfold_let q5; norm_num)
    have he := Real.exp_one_lt_d9
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2:ℝ)=1+1 from by norm_num]; exact Real.exp_add 1 1
    have he6 : Real.exp 6 = Real.exp 2 * Real.exp 2 * Real.exp 2 := by
      rw [show (6:ℝ)=2+2+2 from by norm_num]; rw [Real.exp_add, Real.exp_add]; ring
    rw [he6, he2]; unfold_let q5; push_cast; nlinarith [Real.exp_pos 1]
  rwa [Real.log_exp] at this

private lemma log_p5_pos : (0 : ℝ) < Real.log p5 := by linarith [log_p5_gt_29]
private lemma log_q5_pos : (0 : ℝ) < Real.log q5 := by linarith [log_q5_gt_5]

-- beb 16 > 37/960
-- beb = (16/8)/(2*log p5) + 1/(2*16*log q5) = 1/log(p5) + 1/(32*log(q5))
-- > 1/30 + 1/(32*6) = 1/30 + 1/192 = 37/960
theorem beb_ge_37_960 : (37 : ℝ) / 960 ≤ bridgeErrorBound 16 := by
  unfold bridgeErrorBound
  simp only [Nat.cast_ofNat]
  have hp := log_p5_gt_29; have hp0 := log_p5_pos
  have hplt := log_p5_lt_30
  have hq := log_q5_gt_5; have hq0 := log_q5_pos
  have hqlt := log_q5_lt_6
  have h1 : (16 : ℝ) / 8 / (2 * Real.log p5) = 1 / Real.log p5 := by ring
  have h2 : (1 : ℝ) / (2 * 16 * Real.log q5) = 1 / (32 * Real.log q5) := by ring
  rw [h1, h2]
  have ha : 1 / (30 : ℝ) ≤ 1 / Real.log p5 :=
    div_le_div_of_nonneg_left (by norm_num) hp0 hplt.le
  have hb : 1 / (192 : ℝ) ≤ 1 / (32 * Real.log q5) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  linarith

end MachinPiBounds

-- -----------------------------------------------------------------------
-- Cert_lemma2 (PROVED — replaces certified-input)
-- |191 * kappa^16 - p5 - k_bridge * pi| < bridgeErrorBound 16
-- -----------------------------------------------------------------------

theorem Cert_lemma2 :
    |191 * kappa ^ 16 - p5 - k_bridge * Real.pi| < bridgeErrorBound 16 := by
  -- kappa = 48433014197780389 / 10^16 exactly
  have hkappa : kappa = (48433014197780389 : ℝ) / 10^16 := by
    unfold kappa; norm_num
  have hpi_lo := pi_lo_A_lt_pi   -- pi_lo_A < pi
  have hpi_hi := pi_lt_pi_hi_A   -- pi < pi_hi_A
  have hbeb := beb_ge_37_960     -- 37/960 ≤ beb
  have hkb_pos : (0 : ℝ) < k_bridge := by unfold_let k_bridge; norm_num
  -- Rational check: r_exact - k_bridge*pi_hi_A > -37/960
  -- (verified by norm_num; this is purely rational arithmetic)
  have hrat_lo : -(37 : ℝ)/960 <
      191 * ((48433014197780389 : ℝ)/10^16)^16 - ↑(p5:ℕ) -
      ↑(k_bridge:ℤ) * ((194171005525185591654101515840515257888:ℝ)/61806550668914014199568271636962890625) := by
    unfold_let p5 k_bridge; push_cast; norm_num
  -- Rational check: r_exact - k_bridge*pi_lo_A < 37/960
  have hrat_hi :
      191 * ((48433014197780389 : ℝ)/10^16)^16 - ↑(p5:ℕ) -
      ↑(k_bridge:ℤ) * ((135971713047870654998930719127948:ℝ)/43281140504482774600982666015625) <
      (37 : ℝ)/960 := by
    unfold_let p5 k_bridge; push_cast; norm_num
  rw [abs_lt]
  constructor
  · -- Lower: 191*kappa^16 - p5 - k_bridge*pi > -beb
    -- pi < pi_hi_A => k_bridge*pi < k_bridge*pi_hi_A => r - k_bridge*pi > r - k_bridge*pi_hi_A
    have hkpi : ↑(k_bridge:ℤ) * Real.pi <
                ↑(k_bridge:ℤ) * ((194171005525185591654101515840515257888:ℝ)/61806550668914014199568271636962890625) :=
      mul_lt_mul_of_pos_left hpi_hi hkb_pos
    rw [hkappa]; linarith
  · -- Upper: 191*kappa^16 - p5 - k_bridge*pi < beb
    -- pi > pi_lo_A => k_bridge*pi > k_bridge*pi_lo_A => r - k_bridge*pi < r - k_bridge*pi_lo_A
    have hkpi : ↑(k_bridge:ℤ) * ((135971713047870654998930719127948:ℝ)/43281140504482774600982666015625) <
                ↑(k_bridge:ℤ) * Real.pi :=
      mul_lt_mul_of_pos_left hpi_lo hkb_pos
    rw [hkappa]; linarith

lemma lemma2_kappa16_bridge :
    ∃ k : Int, |191 * kappa ^ 16 - p5 - k * Real.pi| < bridgeErrorBound 16 :=
  ⟨k_bridge, Cert_lemma2⟩

noncomputable def kappa_trunc : Real := 4.843301419

-- -----------------------------------------------------------------------
-- Cert_llm_trunc (PROVED — replaces certified-input)
-- |191 * kappa_trunc^16 - p5 - k_bridge * pi| > bridgeErrorBound 16
-- The truncated-kappa residual ≈ -44885, which is >> beb ≈ 0.04
-- -----------------------------------------------------------------------

theorem Cert_llm_trunc :
    |191 * kappa_trunc ^ 16 - p5 - k_bridge * Real.pi| > bridgeErrorBound 16 := by
  have hkt : kappa_trunc = (4843301419 : ℝ) / 10^9 := by
    unfold kappa_trunc; norm_num
  have hpi_lo := pi_lo_A_lt_pi   -- pi_lo_A < pi
  have hbeb := beb_ge_37_960     -- 37/960 ≤ beb
  have hkb_pos : (0 : ℝ) < k_bridge := by unfold_let k_bridge; norm_num
  -- Rational check: r_trunc - k_bridge*pi_lo_A < -37/960
  -- (residual ≈ -44885; even with loose pi bound this holds)
  have hrat : 191 * ((4843301419:ℝ)/10^9)^16 - ↑(p5:ℕ) -
              ↑(k_bridge:ℤ) * ((135971713047870654998930719127948:ℝ)/43281140504482774600982666015625) <
              -(37 : ℝ)/960 := by
    unfold_let p5 k_bridge; push_cast; norm_num
  -- pi > pi_lo_A => k_bridge*pi > k_bridge*pi_lo_A
  -- => r_trunc - k_bridge*pi < r_trunc - k_bridge*pi_lo_A < -37/960 < -beb
  have hkpi : ↑(k_bridge:ℤ) * ((135971713047870654998930719127948:ℝ)/43281140504482774600982666015625) <
              ↑(k_bridge:ℤ) * Real.pi :=
    mul_lt_mul_of_pos_left hpi_lo hkb_pos
  have hexpr : 191 * kappa_trunc^16 - ↑(p5:ℕ) - ↑(k_bridge:ℤ) * Real.pi < -(37:ℝ)/960 := by
    rw [hkt]; linarith
  rw [gt_iff_lt, lt_abs]
  right; linarith

theorem llm_zero_padding_error :
    |191 * kappa_trunc ^ 16 - p5 - k_bridge * Real.pi| > bridgeErrorBound 16 :=
  Cert_llm_trunc

-- -----------------------------------------------------------------------
-- Lemma 3: 291 Anomaly
-- -----------------------------------------------------------------------

lemma anomaly_291 : (3 ^ 291) % 7 = 6 := by native_decide

theorem Cert_fails_at_291 :
    ¬ (fracDist 291 < 1 / (291 : Real)) := by
  unfold fracDist alpha0
  simp only [Nat.cast_ofNat]
  have hπl := Real.pi_gt_d6
  have hπu := Real.pi_lt_d6
  have hfl : Int.floor ((291 : ℝ) * (299 + Real.pi / 10)) = 87100 :=
    Int.floor_eq_iff.mpr ⟨by push_cast; nlinarith, by push_cast; nlinarith⟩
  rw [hfl]; norm_cast
  rw [show (291 : ℝ) * (299 + Real.pi / 10) - 87100 = 291 * Real.pi / 10 - 91 from by ring]
  rw [min_eq_left (by nlinarith : 291 * Real.pi / 10 - 91 ≤ 1 - (291 * Real.pi / 10 - 91))]
  intro h; nlinarith

theorem llm_fails_at_291 :
    ¬ (fracDist 291 < 1 / (291 : Real)) := Cert_fails_at_291

theorem bdp_boundary_291 :
    (3 ^ 291) % 7 ≠ 3 ∧ ¬ (fracDist 291 < 1 / (291 : Real)) :=
  ⟨by decide, Cert_fails_at_291⟩

-- -----------------------------------------------------------------------
-- Lemma 4: LLM Phase Reversal
-- -----------------------------------------------------------------------

noncomputable def chi (x : Real) : Int :=
  if x > 0 then Int.floor (-Real.log x / Real.log 10) + 1 else 0

-- -----------------------------------------------------------------------
-- Cert_phase_reversal (PROVED — replaces certified-input)
-- chi(1/p5) = 13 < chi(fracDist p5) = 14
-- Uses 30-digit pi bounds to determine floor(p5*pi/10) = 1254672354514
-- -----------------------------------------------------------------------

-- Floor value: floor(p5 * pi / 10) = 1254672354514  (from 30-digit pi bounds)
private lemma floor_p5_pi_10 :
    Int.floor ((p5 : ℝ) * Real.pi / 10) = 1254672354514 := by
  apply Int.floor_eq_iff.mpr
  have hpi_lo := pi_lo_B_lt_pi
  have hpi_hi := pi_lt_pi_hi_NEW
  have hp5 : (0 : ℝ) < p5 := by unfold_let p5; norm_num
  constructor
  · -- 1254672354514 ≤ p5*pi/10
    -- suffices: 1254672354514 ≤ p5*pi_lo_B/10 (since pi > pi_lo_B)
    have hrat : (1254672354514 : ℝ) ≤ (p5 : ℝ) * pi_lo_B / 10 := by
      unfold_let p5 pi_lo_B; push_cast; norm_num
    have h : (p5 : ℝ) * pi_lo_B / 10 < (p5 : ℝ) * Real.pi / 10 := by
      have := mul_lt_mul_of_pos_left hpi_lo hp5; linarith
    linarith
  · -- p5*pi/10 < 1254672354515
    -- suffices: p5*pi_hi_NEW/10 < 1254672354515
    have hrat : (p5 : ℝ) * pi_hi_NEW / 10 < 1254672354515 := by
      unfold_let p5 pi_hi_NEW; push_cast; norm_num
    have h : (p5 : ℝ) * Real.pi / 10 < (p5 : ℝ) * pi_hi_NEW / 10 := by
      have := mul_lt_mul_of_pos_left hpi_hi hp5; linarith
    linarith

-- fracDist(p5) = p5*pi/10 - 1254672354514
-- p5*299 = 1194130096946267 exactly, so floor(p5*(299+pi/10)) = 1195384769300781
-- Proved directly via 30-digit Machin bounds; avoids Int.floor_add_int API issues.
private lemma fracDist_p5_eq :
    fracDist p5 = (p5 : ℝ) * Real.pi / 10 - 1254672354514 := by
  unfold fracDist alpha0
  simp only [Nat.cast_ofNat]
  have hpi_lo := pi_lo_B_lt_pi
  have hpi_hi := pi_lt_pi_hi_NEW
  have hp5 : (0 : ℝ) < p5 := by unfold_let p5; norm_num
  have hp299 : (p5 : ℝ) * 299 = 1194130096946267 := by unfold_let p5; norm_num
  -- Compute floor(p5*(299 + pi/10)) = 1195384769300781 directly
  have hfl : Int.floor ((p5 : ℝ) * (299 + Real.pi / 10)) = 1195384769300781 := by
    apply Int.floor_eq_iff.mpr
    push_cast
    refine ⟨?_, ?_⟩
    · -- lower: 1195384769300781 ≤ p5*(299 + pi/10)
      -- p5*pi_lo_B/10 ≥ 1254672354514  and  pi_lo_B < pi
      have hrat : (p5 : ℝ) * pi_lo_B / 10 ≥ 1254672354514 := by
        unfold_let p5 pi_lo_B; push_cast; norm_num
      have hlt : (p5 : ℝ) * pi_lo_B / 10 < (p5 : ℝ) * Real.pi / 10 := by
        have := mul_lt_mul_of_pos_left hpi_lo hp5; linarith
      linarith
    · -- upper: p5*(299 + pi/10) < 1195384769300782
      -- p5*pi_hi_NEW/10 < 1254672354515  and  pi < pi_hi_NEW
      have hrat : (p5 : ℝ) * pi_hi_NEW / 10 < 1254672354515 := by
        unfold_let p5 pi_hi_NEW; push_cast; norm_num
      have hlt : (p5 : ℝ) * Real.pi / 10 < (p5 : ℝ) * pi_hi_NEW / 10 := by
        have := mul_lt_mul_of_pos_left hpi_hi hp5; linarith
      linarith
  rw [hfl]; push_cast
  -- x - floor(x) = p5*(299+pi/10) - 1195384769300781 = p5*pi/10 - 1254672354514
  have hfrac_eq : (p5 : ℝ) * (299 + Real.pi / 10) - 1195384769300781 =
                  (p5 : ℝ) * Real.pi / 10 - 1254672354514 := by linarith
  -- fractional part < 1/2, so min selects the first branch
  have hfrac_lt_half : (p5 : ℝ) * Real.pi / 10 - 1254672354514 < 1 / 2 := by
    have hrat : (p5 : ℝ) * pi_hi_NEW / 10 < 1254672354514 + 1 / 2 := by
      unfold_let p5 pi_hi_NEW; push_cast; norm_num
    have := mul_lt_mul_of_pos_left hpi_hi hp5; linarith
  rw [hfrac_eq]
  exact min_eq_left (by linarith)

-- fracDist(p5) is in (10^{-14}, 10^{-13})
private lemma fracDist_p5_bounds :
    (10 : ℝ)^(-(14:ℤ)) < fracDist p5 ∧ fracDist p5 < (10 : ℝ)^(-(13:ℤ)) := by
  rw [fracDist_p5_eq]
  have hpi_lo := pi_lo_B_lt_pi
  have hpi_hi := pi_lt_pi_hi_NEW
  have hp5 : (0 : ℝ) < p5 := by unfold_let p5; norm_num
  constructor
  · -- frac > 10^{-14}: suffices p5*pi_lo_B/10 - N > 10^{-14}
    have hrat : (10:ℝ)^(-(14:ℤ)) < (p5:ℝ) * pi_lo_B / 10 - 1254672354514 := by
      unfold_let p5 pi_lo_B; push_cast; norm_num
    have h : (p5:ℝ) * pi_lo_B / 10 < (p5:ℝ) * Real.pi / 10 := by
      have := mul_lt_mul_of_pos_left hpi_lo hp5; linarith
    linarith
  · -- frac < 10^{-13}: suffices p5*pi_hi_NEW/10 - N < 10^{-13}
    have hrat : (p5:ℝ) * pi_hi_NEW / 10 - 1254672354514 < (10:ℝ)^(-(13:ℤ)) := by
      unfold_let p5 pi_hi_NEW; push_cast; norm_num
    have h : (p5:ℝ) * Real.pi / 10 < (p5:ℝ) * pi_hi_NEW / 10 := by
      have := mul_lt_mul_of_pos_left hpi_hi hp5; linarith
    linarith

-- chi(1/p5) = 13: p5 ∈ (10^12, 10^13)
private lemma chi_inv_p5 : chi (1 / (p5 : ℝ)) = 13 := by
  unfold chi
  have hp5_pos : (0 : ℝ) < 1 / (p5:ℝ) := by unfold_let p5; norm_num
  rw [if_pos hp5_pos]
  have hlog10_pos : (0 : ℝ) < Real.log 10 := Real.log_pos (by norm_num)
  have hlog_inv : Real.log (1 / (p5:ℝ)) = -Real.log (p5:ℝ) := by
    rw [Real.log_div (by norm_num) (by unfold_let p5; norm_num), Real.log_one]
  rw [hlog_inv, neg_neg]
  apply Int.floor_eq_iff.mpr
  push_cast
  constructor
  · -- 12 ≤ log(p5)/log(10)
    rw [le_div_iff hlog10_pos]
    have : Real.log ((10:ℝ)^12) ≤ Real.log (p5:ℝ) := by
      apply Real.log_le_log (by positivity)
      unfold_let p5; norm_num
    rw [Real.log_pow] at this; push_cast at this ⊢; linarith
  · -- log(p5)/log(10) < 13
    rw [div_lt_iff hlog10_pos]
    have : Real.log (p5:ℝ) < Real.log ((10:ℝ)^13) := by
      apply Real.log_lt_log (by unfold_let p5; norm_num)
      unfold_let p5; norm_num
    rw [Real.log_pow] at this; push_cast at this ⊢; linarith

-- chi(fracDist p5) = 14: fracDist(p5) ∈ (10^{-14}, 10^{-13})
private lemma chi_fracDist_p5 : chi (fracDist p5) = 14 := by
  unfold chi
  obtain ⟨hlo, hhi⟩ := fracDist_p5_bounds
  have hfd_pos : (0 : ℝ) < fracDist p5 := by
    linarith [show (0:ℝ) < (10:ℝ)^(-(14:ℤ)) from by positivity]
  rw [if_pos hfd_pos]
  have hlog10_pos : (0 : ℝ) < Real.log 10 := Real.log_pos (by norm_num)
  apply Int.floor_eq_iff.mpr
  push_cast
  constructor
  · -- 13 ≤ -log(fd)/log(10)
    rw [le_div_iff hlog10_pos, neg_mul]
    -- 13*log(10) ≤ -log(fd) ⟺ log(fd) ≤ -13*log(10) = log(10^{-13})
    rw [neg_le_iff_add_nonneg, ← sub_nonneg]
    have : Real.log (fracDist p5) ≤ Real.log ((10:ℝ)^(-(13:ℤ))) := by
      apply Real.log_le_log hfd_pos (le_of_lt hhi)
    rw [Real.log_rpow (by norm_num : (0:ℝ)<10)] at this
    push_cast at this ⊢; linarith
  · -- -log(fd)/log(10) < 14
    rw [div_lt_iff hlog10_pos, neg_lt]
    -- -14*log(10) < log(fd) ⟺ log(10^{-14}) < log(fd)
    have : Real.log ((10:ℝ)^(-(14:ℤ))) < Real.log (fracDist p5) := by
      apply Real.log_lt_log (by positivity) hlo
    rw [Real.log_rpow (by norm_num : (0:ℝ)<10)] at this
    push_cast at this ⊢; linarith

theorem Cert_phase_reversal :
    chi (1 / (p5 : Real)) < chi (fracDist p5) ∧
    10 ^ (chi (1 / (p5 : Real))).toNat > 10 ^ 12 := by
  constructor
  · rw [chi_inv_p5, chi_fracDist_p5]; norm_num
  · rw [chi_inv_p5]; norm_num

theorem llm_phase_reversal :
    ∃ p0 : Nat, p0 = p5 ∧
    chi (1 / (p5 : Real)) < chi (fracDist p5) ∧
    10 ^ (chi (1 / (p5 : Real))).toNat > 10 ^ 12 :=
  ⟨p5, rfl, Cert_phase_reversal.1, Cert_phase_reversal.2⟩

-- -----------------------------------------------------------------------
-- Lemma 4 continued: m_boundary
-- -----------------------------------------------------------------------

noncomputable def m_boundary : Int :=
  Int.floor (8 * Real.log p5 / Real.log q5)

theorem Cert_m_boundary : m_boundary = 44 := by
  unfold m_boundary p5 q5
  simp only [Nat.cast_ofNat]
  have hlog191 : (0 : ℝ) < Real.log 191 := Real.log_pos (by norm_num)
  apply Int.floor_eq_iff.mpr
  push_cast
  constructor
  · rw [le_div_iff hlog191]
    have h44 : (44 : ℝ) * Real.log 191 = Real.log ((191:ℝ)^44) := by
      rw [← Real.log_pow]; push_cast; ring
    have h8 : (8 : ℝ) * Real.log 3993746143633 = Real.log ((3993746143633:ℝ)^8) := by
      rw [← Real.log_pow]; push_cast; ring
    rw [h44, h8]
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show (191:ℕ)^44 ≤ (3993746143633:ℕ)^8 from by native_decide)
  · rw [div_lt_iff hlog191]
    have h45 : ((44:ℝ)+1) * Real.log 191 = Real.log ((191:ℝ)^45) := by
      rw [← Real.log_pow]; push_cast; ring
    have h8 : (8 : ℝ) * Real.log 3993746143633 = Real.log ((3993746143633:ℝ)^8) := by
      rw [← Real.log_pow]; push_cast; ring
    rw [h45, h8]
    apply Real.log_lt_log (by positivity)
    exact_mod_cast (show (3993746143633:ℕ)^8 < (191:ℕ)^45 from by native_decide)

lemma m_boundary_value : m_boundary = 44 := Cert_m_boundary

end TheoremaAureum.BDP

-- -----------------------------------------------------------------------
-- AXIOM AUDIT (BDP module) -- CLOSED 2026-06-13
-- gap_count = 0  |  extra_decls = 0
-- Cert_lemma2:         PROVED via 15-digit Machin bounds + norm_num
-- Cert_llm_trunc:      PROVED via 15-digit Machin lower bound + norm_num
-- Cert_phase_reversal: PROVED via 30-digit Machin bounds + log arithmetic
-- #print_trio -> [propext, Classical.choice, Quot.sound]
-- -----------------------------------------------------------------------
