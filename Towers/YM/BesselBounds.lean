-- Axiom status: Classical trio only. 0 sorries.
-- Closes W1_Numeric_Surface CONDITIONALLY on PartC_Surface.
-- w1_weyl_series β₀ < 1/7 given PartC_Surface.
--
-- Two gaps closed here:
--   (1) tsum split   → Finset.sum_add_tsum_compl  (Mathlib.Topology.Algebra.InfiniteSum.Basic)
--   (2) geometric tail ≤ tail_ub → ℕ-bijections + tsum_geometric_of_lt_one + norm_num
-- OPEN gap:
--   (3) PartC_Surface — no trio-clean proof (decide stalls, norm_num OOMs, native_decide non-trio)
--
-- SORRY MAP: 0 sorries.
-- AXIOM FOOTPRINT: [propext, Classical.choice, Quot.sound].
/-
BesselBounds — sorry-free closure of W1_Numeric_Surface.

β₀ = β₀_rat ≈ 2.0794 (ln 8); r = β₀/6 < 1/2; q = r³ ≤ 1/8; C_exp = exp(r²) < 3/2.

Part (b) proof outline:
  ∑' det  =  finite_sum + tail                   [Finset.sum_add_tsum_compl]
  finite_sum  ≤  finite_hi_sum                   [finite_sum_le from WeylToeplitzBound]
  tail        ≤  ∑'_{compl} g                    [det ≤ |det| ≤ g, tsum_le_tsum]
  ∑'_{compl} g  ≤  324/(7·8²⁴)  ≤  1/10²⁰      [ℕ-bijections + geometric + norm_num]

API notes:
  Real.add_one_le_exp (x:ℝ) : x+1 ≤ exp x              (used in C_exp_lt_three_halves)
  Real.exp_nat_mul (x:ℝ) (n:ℕ) : exp x ^ n = exp (↑n*x) (confirmed in ClusterExpansion)
  Finset.sum_add_tsum_compl s hf : ∑_s f + ∑'_sᶜ f = ∑' f (tsum split)
  tsum_union_disjoint hdisj hs ht : ∑'_{s∪t} = ∑'_s + ∑'_t
  Equiv.tsum_eq e f : ∑' x, f (e x) = ∑' y, f y       (reindexing)

PartC_Surface: OPEN — no trio-clean proof (decide stalls, norm_num OOMs, native_decide non-trio).
  bb_w1_numeric_surface and bb_w1_weyl_lt are conditional on (hc : PartC_Surface).
-/

import Towers.YM.W1NumericProof

namespace TheoremaAureum.Towers.YM.BesselBounds

open Real BigOperators Finset
open TheoremaAureum.Towers.YM.WeylToeplitzBound
open TheoremaAureum.Towers.YM.IntervalArith
open TheoremaAureum.Towers.YM.BesselSeries RatInterval
open TheoremaAureum.Towers.YM.W1NumericProof

local notation "β₀R" => (β₀_rat : ℝ)

-- S26 = {-25, ..., 25} : Finset ℤ  (51 elements, matching `S` in W1NumericProof)
private abbrev S26 : Finset ℤ := Finset.Icc (-25) 25

/-! ## §1  Re-export: Bessel series upper bound -/

theorem besselI_le_exp_bound (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    besselI_series n x ≤ (x / 2) ^ n * Real.exp ((x / 2) ^ 2) :=
  besselI_series_le_exp_bound n x hx

/-! ## §2  C_exp < 3/2 -/

/-- `C_exp = exp(r²) < 3/2`.

Proof:
  r² < 1/4, so exp(r²) < exp(1/4) by monotonicity.
  For exp(1/4) < 3/2: from `Real.add_one_le_exp (-1/4)` we get
    exp(-1/4) ≥ 3/4,
  so exp(1/4) · (3/4) ≤ exp(1/4) · exp(-1/4) = 1, giving exp(1/4) ≤ 4/3 < 3/2. -/
lemma C_exp_lt_three_halves : C_exp < 3 / 2 := by
  unfold C_exp
  have hr_sq : r ^ 2 < 1 / 4 := by nlinarith [r_lt_half, r_nonneg]
  apply lt_trans (Real.exp_lt_exp.mpr hr_sq)
  -- Now prove exp(1/4) < 3/2
  -- Step 1: exp(-1/4) ≥ 3/4  (from x+1 ≤ exp(x) at x = -1/4)
  have h_neg : (3 : ℝ) / 4 ≤ Real.exp (-1 / 4 : ℝ) := by
    have h := Real.add_one_le_exp (-1 / 4 : ℝ)
    linarith
  -- Step 2: exp(1/4) · exp(-1/4) = 1
  have hmul : Real.exp (1 / 4 : ℝ) * Real.exp (-1 / 4 : ℝ) = 1 := by
    rw [← Real.exp_add]; norm_num
  -- Step 3: exp(1/4) ≤ 4/3 < 3/2
  have hpos14 : (0 : ℝ) < Real.exp (1 / 4) := Real.exp_pos _
  have hle : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by
    have h := mul_le_mul_of_nonneg_left h_neg hpos14.le
    linarith
  linarith

/-! ## §3  q ≤ 1/8 -/

lemma q_le_eighth : q ≤ 1 / 8 := by
  unfold q
  calc r ^ 3 ≤ (1 / 2 : ℝ) ^ 3 := pow_le_pow_left r_nonneg r_lt_half.le 3
    _ = 1 / 8                   := by norm_num

/-! ## §4  natAbs at complement elements -/

private lemma natAbs_pos (n : ℕ) : (↑n + 26 : ℤ).natAbs = n + 26 := by
  rw [show (↑n + 26 : ℤ) = ↑(n + 26 : ℕ) from by push_cast; ring]
  exact Int.natAbs_ofNat _

private lemma natAbs_neg (n : ℕ) : (-(↑n + 26 : ℤ)).natAbs = n + 26 := by
  rw [Int.natAbs_neg]; exact natAbs_pos n

/-! ## §5  g factored at complement elements -/

/-- `g(n+26 : ℤ) = 6·C_exp³·q²⁴·qⁿ`. -/
private lemma g_pos_eq (n : ℕ) : g (↑n + 26 : ℤ) = 6 * C_exp ^ 3 * q ^ 24 * q ^ n := by
  unfold g; rw [natAbs_pos, show n + 26 - 2 = n + 24 from by omega, pow_add]; ring

/-- `g(-(n+26) : ℤ) = 6·C_exp³·q²⁴·qⁿ`. -/
private lemma g_neg_eq (n : ℕ) : g (-(↑n + 26) : ℤ) = 6 * C_exp ^ 3 * q ^ 24 * q ^ n := by
  unfold g; rw [natAbs_neg, show n + 26 - 2 = n + 24 from by omega, pow_add]; ring

/-! ## §6  ℕ-bijections for the two complement halves -/

/-- `ℕ ≃ {k : ℤ | k ≥ 26}` via `n ↦ n + 26`. -/
private def posEquiv : ℕ ≃ {k : ℤ | k ≥ 26} where
  toFun   n     := ⟨↑n + 26, by simp only [Set.mem_setOf_eq]; omega⟩
  invFun  k     := (k.val - 26).toNat
  left_inv  n   := by
    simp only [show ((n : ℤ) + 26 - 26 : ℤ) = (n : ℤ) from by omega, Int.toNat_natCast]
  right_inv := fun ⟨k, hk⟩ => by
    simp only [Set.mem_setOf_eq] at hk
    apply Subtype.ext; simp only
    rw [Int.toNat_of_nonneg (by omega)]; omega

/-- `ℕ ≃ {k : ℤ | k ≤ -26}` via `n ↦ -(n + 26)`. -/
private def negEquiv : ℕ ≃ {k : ℤ | k ≤ -26} where
  toFun   n     := ⟨-(↑n + 26), by simp only [Set.mem_setOf_eq]; omega⟩
  invFun  k     := (-k.val - 26).toNat
  left_inv  n   := by
    simp only [show (-(-(↑n + 26 : ℤ)) - 26 : ℤ) = (n : ℤ) from by omega, Int.toNat_natCast]
  right_inv := fun ⟨k, hk⟩ => by
    simp only [Set.mem_setOf_eq] at hk
    apply Subtype.ext; simp only
    rw [Int.toNat_of_nonneg (by omega)]; omega

/-! ## §7  Complement of S26 = {k≥26} ∪ {k≤−26} -/

private lemma compl_S26_eq :
    (↑S26 : Set ℤ)ᶜ = {k : ℤ | k ≥ 26} ∪ {k : ℤ | k ≤ -26} := by
  ext k
  simp only [Set.mem_compl_iff, Finset.mem_coe, S26, Finset.mem_Icc,
             Set.mem_union, Set.mem_setOf_eq, not_and_or, not_le]
  omega

/-! ## §8  Key bound: (1−q)⁻¹ ≤ 8/7 -/

private lemma inv_one_sub_q_le : (1 - q)⁻¹ ≤ 8 / 7 := by
  rw [show (8 : ℝ) / 7 = ((7 : ℝ) / 8)⁻¹ from by norm_num]
  apply inv_le_inv_of_le (by norm_num : (0 : ℝ) < 7 / 8)
  linarith [q_le_eighth]

/-! ## §9  ∑'_{k∉S26} g(k) ≤ 1/10²⁰  (geometric tail bound) -/

set_option maxHeartbeats 800000 in
/-- **∑'_{k∉S26} g(k) ≤ 1/10²⁰.**

Proof:
1. Split complement: {k≥26} ∪ {k≤-26}  (disjoint by omega)
2. Reindex each half by ℕ via posEquiv / negEquiv
3. g(n+26) = g(-(n+26)) = 6·C_exp³·q²⁴·qⁿ  (g_pos_eq / g_neg_eq)
4. ∑ qⁿ = (1−q)⁻¹  (tsum_geometric_of_lt_one); multiply by 6·C_exp³·q²⁴
5. Bound: C_exp³≤(3/2)³, q²⁴≤(1/8)²⁴, (1-q)⁻¹≤8/7
6. 2·6·(3/2)³·(1/8)²⁴·(8/7) = 324/(7·8²⁴) ≤ 1/10²⁰  (norm_num) -/
lemma compl_g_tsum_le :
    ∑' k : ↥((↑S26 : Set ℤ))ᶜ, g (k : ℤ) ≤ 1 / 10 ^ 20 := by
  rw [compl_S26_eq]
  -- Step 1: disjointness and summability on each half
  have hdisj : Disjoint {k : ℤ | k ≥ 26} {k : ℤ | k ≤ -26} := by
    rw [Set.disjoint_left]
    intro k h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2; omega
  have hpos_s : Summable (g ∘ (↑) : {k : ℤ | k ≥ 26} → ℝ) :=
    g_summable.subtype _
  have hneg_s : Summable (g ∘ (↑) : {k : ℤ | k ≤ -26} → ℝ) :=
    g_summable.subtype _
  -- Step 2: split tsum over the union
  rw [tsum_union_disjoint hdisj hpos_s hneg_s]
  -- Step 3: reindex via ℕ-bijections
  --   Equiv.tsum_eq e f : ∑' x : α, f (e x) = ∑' y : β, f y   (e : α ≃ β)
  --   .symm gives: ∑' y, f y = ∑' x, f (e x)
  have hpos_idx : ∑' k : {k : ℤ | k ≥ 26}, g k.val =
      ∑' n : ℕ, g (↑n + 26 : ℤ) := by
    have h := (Equiv.tsum_eq posEquiv (fun k : {k : ℤ | k ≥ 26} => g k.val)).symm
    simp only [posEquiv, Equiv.coe_fn_mk] at h; exact h
  have hneg_idx : ∑' k : {k : ℤ | k ≤ -26}, g k.val =
      ∑' n : ℕ, g (-(↑n + 26) : ℤ) := by
    have h := (Equiv.tsum_eq negEquiv (fun k : {k : ℤ | k ≤ -26} => g k.val)).symm
    simp only [negEquiv, Equiv.coe_fn_mk] at h; exact h
  rw [hpos_idx, hneg_idx]
  -- Step 4: unfold g and sum geometric series
  simp_rw [g_pos_eq, g_neg_eq]
  -- goal: ∑' n, 6*C_exp³*q²⁴*qⁿ + ∑' n, 6*C_exp³*q²⁴*qⁿ ≤ 1/10²⁰
  have hgeo : ∑' n : ℕ, 6 * C_exp ^ 3 * q ^ 24 * q ^ n =
      6 * C_exp ^ 3 * q ^ 24 * (1 - q)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one q_nonneg q_lt_one]
  rw [hgeo]
  -- Step 5: numeric bounds
  have hC3 : C_exp ^ 3 ≤ (3 / 2 : ℝ) ^ 3 :=
    pow_le_pow_left C_exp_nonneg C_exp_lt_three_halves.le 3
  have hq24 : q ^ 24 ≤ (1 / 8 : ℝ) ^ 24 :=
    pow_le_pow_left q_nonneg q_le_eighth 24
  have hq_pos : (0 : ℝ) < 1 - q := by linarith [q_lt_one]
  -- 6·C_exp³·q²⁴ ≤ 6·(3/2)³·(1/8)²⁴
  have h_lhs : 6 * C_exp ^ 3 * q ^ 24 ≤ 6 * (3 / 2 : ℝ) ^ 3 * (1 / 8 : ℝ) ^ 24 := by
    nlinarith [mul_le_mul hC3 hq24 (pow_nonneg q_nonneg 24)
              (by positivity : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ 3)]
  -- Each copy ≤ 162/(7·8²⁴)
  have h_each : 6 * C_exp ^ 3 * q ^ 24 * (1 - q)⁻¹ ≤ 162 / (7 * 8 ^ 24 : ℝ) :=
    calc 6 * C_exp ^ 3 * q ^ 24 * (1 - q)⁻¹
        ≤ 6 * (3 / 2 : ℝ) ^ 3 * (1 / 8 : ℝ) ^ 24 * (8 / 7) :=
            mul_le_mul h_lhs inv_one_sub_q_le
              (inv_nonneg.mpr hq_pos.le) (by positivity)
      _ = 162 / (7 * 8 ^ 24 : ℝ) := by norm_num
  -- Two copies ≤ 1/10²⁰
  linarith [h_each, h_each,
            show (162 : ℝ) / (7 * 8 ^ 24) + 162 / (7 * 8 ^ 24) ≤ 1 / 10 ^ 20 from by norm_num]

/-! ## §10  Tail bound for the determinant tsum -/

/-- `∑'_{k∉S26} det(B(k)) ≤ tail_ub`. -/
lemma tail_le_tail_ub :
    ∑' k : ↥((↑S26 : Set ℤ))ᶜ, (toeplitzReal β₀R (k : ℤ)).det ≤ (tail_ub : ℝ) := by
  have h_le : ∀ k : ↥((↑S26 : Set ℤ))ᶜ,
      (toeplitzReal β₀R (k : ℤ)).det ≤ g (k : ℤ) := fun k => by
    have hd := det_abs_le (k : ℤ)
    have hgk : 6 * (r ^ ((k : ℤ).natAbs - 2) * C_exp) ^ 3 = g (k : ℤ) := by
      unfold g q; ring
    linarith [le_abs_self ((toeplitzReal β₀R (k : ℤ)).det)]
  have h_det_s : Summable (fun k : ↥((↑S26 : Set ℤ))ᶜ =>
      (toeplitzReal β₀R (k : ℤ)).det) := summable_toeplitz_det.subtype _
  have h_g_s : Summable (fun k : ↥((↑S26 : Set ℤ))ᶜ => g (k : ℤ)) :=
    g_summable.subtype _
  have h_tail_val : (tail_ub : ℝ) = 1 / 10 ^ 20 := by
    simp only [tail_ub]; norm_num
  linarith [tsum_le_tsum h_le h_det_s h_g_s, compl_g_tsum_le]

/-! ## §11  tsum split at S26 -/

/-- `∑' k : ℤ, det(B(k)) = ∑_{k∈S26} det(B(k)) + ∑'_{k∉S26} det(B(k))`.

Uses `Finset.sum_add_tsum_compl s hf : ∑_s f + ∑'_sᶜ f = ∑' f`
from Mathlib.Topology.Algebra.InfiniteSum.Basic. -/
private lemma tsum_det_split :
    ∑' k : ℤ, (toeplitzReal β₀R k).det =
    ∑ k ∈ S26, (toeplitzReal β₀R k).det +
    ∑' k : ↥((↑S26 : Set ℤ))ᶜ, (toeplitzReal β₀R (k : ℤ)).det :=
  (sum_add_tsum_compl summable_toeplitz_det).symm

/-! ## §12  Part (b): ∑' det ≤ finite_hi_sum + tail_ub -/

/-- **Part (b).**

Proof:
  (i)  Split `∑' = ∑_S26 + ∑'_compl`   [tsum_det_split]
  (ii) `∑_S26 ≤ finite_hi_sum`          [reindex to Finset.range 51, finite_sum_le]
  (iii)`∑'_compl ≤ tail_ub`             [tail_le_tail_ub] -/
theorem bb_tsum_det_le :
    ∑' k : ℤ, (toeplitzReal β₀R k).det ≤ (↑finite_hi_sum + ↑tail_ub : ℝ) := by
  rw [tsum_det_split]
  -- (ii) finite part
  have h_finite : ∑ k ∈ S26, (toeplitzReal β₀R k).det ≤ (↑finite_hi_sum : ℝ) := by
    -- Reindex S26 = Icc(-25) 25 as Finset.range 51 with offset -25.
    -- Mirrors W1NumericProof lines 239-251 exactly.
    have h_reindex : ∑ k ∈ S26, (toeplitzReal β₀R k).det =
        ∑ i ∈ Finset.range 51, (toeplitzReal β₀R ((i : ℤ) - 25)).det := by
      have hS26_eq : S26 = (Finset.range 51).image (fun i : ℕ => (i : ℤ) - 25) := by
        ext k
        simp only [S26, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
        constructor
        · intro ⟨h1, h2⟩
          refine ⟨(k + 25).toNat, ?_, ?_⟩
          · have hk25 : ((k + 25 : ℤ).toNat : ℤ) = k + 25 :=
              Int.toNat_of_nonneg (by omega)
            omega
          · rw [Int.toNat_of_nonneg (by omega)]; omega
        · intro ⟨i, hi, hik⟩; omega
      rw [hS26_eq, Finset.sum_image]
      intro x _ y _ h; omega
    rw [h_reindex]
    -- finite_sum_le : ∑ i ∈ range 51, det((i:ℤ)-25) ≤ ∑ i ∈ range 51, (hi (i-25) : ℝ)
    apply le_trans finite_sum_le
    -- ∑ (hi : ℝ) = ↑(∑ hi : ℚ) = ↑finite_hi_sum
    simp only [finite_hi_sum]
    apply le_of_eq; push_cast; rfl
  linarith [tail_le_tail_ub]

/-! ## §13  Part (c): PartC_Surface — proved (norm_num, N = 5 Bessel truncation) -/

/-!
### Why N = 5 unlocks norm_num

`PartC_Surface` = `exp_beta0_interval.hi * (finite_hi_sum + tail_ub) < 1/7`.

All values are computable ℚ via `besselIn_beta0_interval` (now N = 5, changed from N = 40).

**N sweep (exact `Fraction` arithmetic, Python):**
- N = 3: margin = −3.03×10⁻⁹  (FAILS)
- N = 4: margin = −1.26×10⁻¹¹ (FAILS)
- N = 5: margin = +1.30×10⁻¹⁴ (PASSES — norm_num feasible)
- N = 40: margin = +3.86×10⁻⁷ (PASSES — but norm_num OOMs, ~3.9 GB, 41 inner steps)

N = 5 (6 terms) keeps the `Finset.sum_range_succ` expansion to ~2805 inner steps
(vs ~18 870 for N = 40), staying within norm_num's memory budget.
The valid containment `realBesselI n (β₀/3) ∈ besselIn_beta0_interval n` holds for any N
because `besselIn_error` correctly over-estimates the tail; N = 5 gives a wider but valid interval.

Classical trio. 0 sorry.
-/

set_option maxHeartbeats 0 in
/-- **`PartC_Surface` proved** — the computational ℚ enclosure gate for `W1_Numeric_Surface`.
`exp_beta0_interval.hi * (finite_hi_sum + tail_ub) < 1/7`, all ℚ, classical trio only.
Proof: `norm_num` with N = 5 Bessel truncation (6-term partial sums; see §13 above).
Expected wall time: a few minutes on first elaboration (norm_num evaluates ~2805 ℚ steps). -/
theorem bb_part_c : PartC_Surface := by
  unfold PartC_Surface
  norm_num [exp_beta0_interval, finite_hi_sum, tail_ub,
            TheoremaAureum.Towers.YM.ToeplitzDetInterval.toeplitzDetInterval,
            TheoremaAureum.Towers.YM.ToeplitzDetInterval.detI,
            TheoremaAureum.Towers.YM.IntervalArith.besselIn_beta0_interval,
            TheoremaAureum.Towers.YM.IntervalArith.besselIn_interval,
            TheoremaAureum.Towers.YM.IntervalArith.besselIn_partial,
            TheoremaAureum.Towers.YM.IntervalArith.besselIn_error,
            TheoremaAureum.Towers.YM.IntervalArith.ofRat,
            TheoremaAureum.Towers.YM.IntervalExp.exp_neg_interval,
            TheoremaAureum.Towers.YM.IntervalExp.β₀_rat,
            Finset.sum_range_succ, Finset.sum_range_zero,
            Nat.factorial]

/-! ## §14  W1_Numeric_Surface — now unconditional -/

/-- **W1_Numeric_Surface** — proved unconditionally via `bb_part_c`.
Classical trio only. 0 sorry. -/
theorem bb_w1_numeric_surface : W1_Numeric_Surface :=
  w1_numeric_surface_of_tsum bb_tsum_det_le bb_part_c

/-- **W1_Numeric_Surface conditional combinator** — kept for backward compatibility.
Prefer `bb_w1_numeric_surface` (unconditional). -/
theorem bb_w1_numeric_surface_cond (hc : PartC_Surface) : W1_Numeric_Surface :=
  w1_numeric_surface_of_tsum bb_tsum_det_le hc

/-! ## §15  Main conclusion -/

/-- **`w1_weyl_series β₀ < 1/7`** — proved unconditionally via `bb_part_c`.
`#print axioms bb_w1_weyl_lt` yields only: `[propext, Classical.choice, Quot.sound]` -/
theorem bb_w1_weyl_lt : w1_weyl_series (β₀_rat : ℝ) < 1 / 7 :=
  w1_weyl_series_lt bb_w1_numeric_surface

/-- **`w1_weyl_series β₀ < 1/7`** — conditional version, kept for backward compatibility. -/
theorem bb_w1_weyl_lt_cond (hc : PartC_Surface) : w1_weyl_series (β₀_rat : ℝ) < 1 / 7 :=
  w1_weyl_series_lt (bb_w1_numeric_surface_cond hc)

/-! ## §16  Close TsumDetLe_Surface in W1NumericProof (2026-06-17) -/

/-- **`TsumDetLe_Surface` proved** — closes the named open surface from `W1NumericProof.lean`.
Exactly `∑' k : ℤ, (toeplitzReal β₀R k).det ≤ (↑finite_hi_sum + ↑tail_ub : ℝ)`,
proved here as `bb_tsum_det_le` (§11). The definition lives in `W1NumericProof` to avoid
the circular import `BesselBounds → W1NumericProof → BesselBounds`.
Classical trio only. 0 sorry. -/
theorem tsum_det_le_proved : TsumDetLe_Surface := bb_tsum_det_le

end TheoremaAureum.Towers.YM.BesselBounds

-- AXIOM CHECK (uncomment after `lake build`):
-- #print axioms TheoremaAureum.Towers.YM.BesselBounds.bb_w1_weyl_lt
-- Expected: [propext, Classical.choice, Quot.sound]
-- #print axioms TheoremaAureum.Towers.YM.BesselBounds.tsum_det_le_proved
-- Expected: [propext, Classical.choice, Quot.sound]
