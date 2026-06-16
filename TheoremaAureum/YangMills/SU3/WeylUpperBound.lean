/-
  Wall 256.2b UPPER — YM/SU3/WeylUpperBound.lean (2026-06-15, gaps closed)

  Statement: If N*(Λ) ≤ C₂·Λ⁴ eventually, then K(t) ≤ 386·C₂/t⁴ for small t > 0.

  GAP 1 CLOSED (2026-06-15):
    Sigma decomp over ⌊casimir⌋₊ strips + Abel summation by parts.
    Defining ps(k) = Σ_{j<k} strip_sum(j) (partial sums), we have
      strip_sum(k) = ps(k+1) - ps(k)
      ps(k+1) ≤ N*(k+1)                [disjoint union of strips ⊆ Weyl sphere]
    Abel: ∑' k, strip_k · rᵏ = (1−r) · ∑' k, ps(k+1) · rᵏ
    (identity from ∑(ps(k+1)−ps(k))·rᵏ = T − (ps(0) + r·T) = (1−r)·T, ps(0)=0)

  GAP 2 CLOSED (2026-06-15):
    ∑(n+1)⁴·rⁿ ≤ 24/(1−r)⁵  (see Polylog.lean for the standalone version).
    Proof: (n+1)⁴ ≤ (n+1)(n+2)(n+3)(n+4) and ∑ C(n+4,4)·rⁿ = 1/(1−r)⁵.

  Full bound:
    TAIL: ≤ ∑ₐₗₗ dim²·r^⌊cas⌋₊ = ∑ₖ stripₖ·rᵏ = (1−r)·T
          T ≤ ∑ₖ N*(k+1)·rᵏ ≤ ∑ₖ (C₂/t⁴ + C₂·(k+1)⁴)·rᵏ
            = C₂/t⁴·(1−r)⁻¹ + C₂·24/(1−r)⁵
          (1−r)·T ≤ C₂/t⁴ + 24C₂/(1−r)⁴ ≤ C₂/t⁴ + 384C₂/t⁴ = 385C₂/t⁴
    HEAD: ≤ N*(⌊1/t⌋₊) ≤ N*(1/t) ≤ C₂/t⁴
    TOTAL: K(t) ≤ 386·C₂/t⁴.

  HONEST CAVEAT: the Weyl hypothesis N*(Λ) ≤ C₂·Λ⁴ (eventually) is an OPEN input —
  SU(3) character theory + asymptotic rep-theory absent from mathlib v4.12.0.
  YM Surface #1: OPEN. No mass-gap claim.

  Self-contained: no imports from YM.SU3.*.
  STATUS: SCAFFOLD — NOT a registered brick.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Order.Filter.AtTopBot

open Filter Real Classical
open scoped BigOperators

namespace SU3WeylUpper

-- ── Self-contained defs ───────────────────────────────────────────────────────

abbrev Weight := ℕ × ℕ

noncomputable def casimir_su3 (w : Weight) : ℝ :=
  ((w.1 * w.1 : ℝ) + w.2 * w.2 + w.1 * w.2 + 3 * w.1 + 3 * w.2) / 3

def dim_su3 (w : Weight) : ℕ :=
  (w.1 + 1) * (w.2 + 1) * (w.1 + w.2 + 2) / 2

noncomputable def N_star (Λ : ℝ) : ℝ :=
  ∑' w : {w : Weight // casimir_su3 w ≤ Λ}, (dim_su3 w.val : ℝ) ^ 2

noncomputable def heat_trace_su3 (t : ℝ) : ℝ :=
  ∑' w : Weight, (dim_su3 w : ℝ) ^ 2 * exp (-t * casimir_su3 w)

-- ── Auxiliary lemmas ──────────────────────────────────────────────────────────

lemma casimir_nonneg (w : Weight) : 0 ≤ casimir_su3 w := by
  simp only [casimir_su3]
  have hm : (0 : ℝ) ≤ w.1 := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ w.2 := Nat.cast_nonneg _
  positivity

lemma finite_casimir_le (Λ : ℝ) : {w : Weight | casimir_su3 w ≤ Λ}.Finite := by
  let N := ⌊Real.sqrt (3 * Λ)⌋₊ + 1
  apply (Finset.finite_toSet (Finset.range N ×ˢ Finset.range N)).subset
  rintro ⟨m, n⟩ hw
  simp only [Set.mem_setOf_eq, casimir_su3, Prod.fst, Prod.snd] at hw
  simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hm2 : (m : ℝ) ^ 2 ≤ 3 * Λ := by
    nlinarith [mul_nonneg hm hn, sq_nonneg (n : ℝ), show (m : ℝ) ^ 2 = m * m from by ring]
  have hn2 : (n : ℝ) ^ 2 ≤ 3 * Λ := by
    nlinarith [mul_nonneg hm hn, sq_nonneg (m : ℝ), show (n : ℝ) ^ 2 = n * n from by ring]
  have hm_le : (m : ℝ) ≤ Real.sqrt (3 * Λ) := by
    rw [← Real.sqrt_sq hm]; exact Real.sqrt_le_sqrt hm2
  have hn_le : (n : ℝ) ≤ Real.sqrt (3 * Λ) := by
    rw [← Real.sqrt_sq hn]; exact Real.sqrt_le_sqrt hn2
  exact ⟨by omega [Nat.le_floor hm_le], by omega [Nat.le_floor hn_le]⟩

lemma N_star_eq_sum (Λ : ℝ) :
    N_star Λ = ∑ w in (finite_casimir_le Λ).toFinset, (dim_su3 w : ℝ) ^ 2 := by
  simp only [N_star]
  set hS := finite_casimir_le Λ
  haveI : Fintype {w : Weight // casimir_su3 w ≤ Λ} := hS.fintype
  rw [tsum_fintype]
  exact Finset.sum_nbij (·.val)
    (fun w _ => hS.mem_toFinset.mpr w.property)
    (fun a _ b _ h => Subtype.ext h)
    (fun b hb =>
      ⟨⟨b, hS.mem_toFinset.mp (Finset.mem_coe.mp hb)⟩,
        Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩)
    (fun w _ => rfl)

lemma N_star_mono {Λ Λ' : ℝ} (h : Λ ≤ Λ') : N_star Λ ≤ N_star Λ' := by
  rw [N_star_eq_sum Λ, N_star_eq_sum Λ']
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro w hw
    exact (finite_casimir_le Λ').mem_toFinset.mpr
      (((finite_casimir_le Λ).mem_toFinset.mp hw).trans h)
  · intro w _ _; exact sq_nonneg _

set_option maxHeartbeats 800000 in
lemma summable_heat_trace (t : ℝ) (ht : 0 < t) :
    Summable (fun w : Weight => (dim_su3 w : ℝ) ^ 2 * exp (-t * casimir_su3 w)) := by
  have hr : ‖Real.exp (-t)‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_one_iff]; linarith
  have hSk : ∀ k : ℕ, Summable (fun m : ℕ => (m : ℝ) ^ k * Real.exp (-t * m)) := fun k => by
    have hgeo := summable_pow_mul_geometric_of_norm_lt_one k hr
    have heq : (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-t) ^ n) =
               (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-t * n)) := by
      ext n; congr 1; rw [← Real.exp_nat_mul (-t) n]; congr 1; ring
    rwa [heq] at hgeo
  have hSf : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ 4 * Real.exp (-t * m)) :=
    (((hSk 4).add ((hSk 3).mul_left 4)).add
      (((hSk 2).mul_left 6).add (((hSk 1).mul_left 4).add (hSk 0)))).congr
    (fun m => by ring)
  apply Summable.of_norm_bounded
    (fun w : ℕ × ℕ => ((w.1 : ℝ) + 1) ^ 4 * Real.exp (-t * w.1) *
                       (((w.2 : ℝ) + 1) ^ 4 * Real.exp (-t * w.2)))
  · have hfn : Summable (fun m : ℕ => ‖((m : ℝ) + 1) ^ 4 * Real.exp (-t * (m : ℝ))‖) := by
      rw [show (fun m : ℕ => ‖((m : ℝ) + 1) ^ 4 * Real.exp (-t * (m : ℝ))‖) =
          fun m : ℕ => ((m : ℝ) + 1) ^ 4 * Real.exp (-t * (m : ℝ)) from by
        ext m; exact Real.norm_of_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)]
      exact hSf
    exact summable_mul_of_summable_norm hfn hfn
  · intro ⟨m, n⟩
    rw [Real.norm_of_nonneg (by positivity)]
    have hdim : (dim_su3 (m, n) : ℝ) ≤ ((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 := by
      have hle : dim_su3 (m, n) * 2 ≤ (m + 1) * (n + 1) * (m + n + 2) :=
        Nat.div_mul_le_self _ _
      nlinarith [show (dim_su3 (m, n) : ℝ) * 2 ≤
          ((m : ℝ) + 1) * ((n : ℝ) + 1) * ((m : ℝ) + n + 2) from by exact_mod_cast hle,
        Nat.cast_nonneg (α := ℝ) (dim_su3 (m, n)),
        mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (Nat.cast_nonneg (α := ℝ) n)]
    have hdim2 : (dim_su3 (m, n) : ℝ) ^ 2 ≤ ((m : ℝ) + 1) ^ 4 * ((n : ℝ) + 1) ^ 4 := by
      nlinarith [sq_nonneg ((dim_su3 (m, n) : ℝ) - ((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2),
        Nat.cast_nonneg (α := ℝ) (dim_su3 (m, n))]
    have hcas : (m : ℝ) + n ≤ casimir_su3 (m, n) := by
      simp only [casimir_su3]
      nlinarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) n,
        mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (Nat.cast_nonneg (α := ℝ) n),
        sq_nonneg (m : ℝ), sq_nonneg (n : ℝ)]
    have hexp : Real.exp (-t * casimir_su3 (m, n)) ≤
                Real.exp (-t * (m : ℝ)) * Real.exp (-t * (n : ℝ)) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hcas ht.le]
    calc (dim_su3 (m, n) : ℝ) ^ 2 * Real.exp (-t * casimir_su3 (m, n))
        ≤ ((m : ℝ) + 1) ^ 4 * ((n : ℝ) + 1) ^ 4 * Real.exp (-t * casimir_su3 (m, n)) :=
            mul_le_mul_of_nonneg_right hdim2 (Real.exp_pos _).le
      _ ≤ ((m : ℝ) + 1) ^ 4 * ((n : ℝ) + 1) ^ 4 *
          (Real.exp (-t * m) * Real.exp (-t * n)) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = ((m : ℝ) + 1) ^ 4 * Real.exp (-t * (m : ℝ)) *
          (((n : ℝ) + 1) ^ 4 * Real.exp (-t * (n : ℝ))) := by ring

-- ── Degree-4 polylogarithm (Gap 2 CLOSED) ────────────────────────────────────

private lemma choose_four_val (k : ℕ) :
    24 * (k + 4).choose 4 = (k + 1) * (k + 2) * (k + 3) * (k + 4) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (k + 4) 4
  simp [Nat.descFactorial, Nat.factorial] at h
  linarith [show (k + 4) * (k + 3) * (k + 2) * (k + 1) =
      (k + 1) * (k + 2) * (k + 3) * (k + 4) from by ring]

/-- ∑_{n≥0} (n+1)⁴·rⁿ ≤ 24/(1−r)⁵ for r ∈ [0, 1). -/
private lemma tsum_pow_four_mul_geometric_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' n : ℕ, ((n : ℝ) + 1) ^ 4 * r ^ n ≤ 24 / (1 - r) ^ 5 := by
  have hr_norm : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0]
  have hSk : ∀ j : ℕ, Summable (fun n : ℕ => (n : ℝ) ^ j * r ^ n) :=
    fun j => summable_pow_mul_geometric_of_norm_lt_one j hr_norm
  have hLHS : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 4 * r ^ n) :=
    ((((hSk 4).add ((hSk 3).mul_left 4)).add
        (((hSk 2).mul_left 6).add (((hSk 1).mul_left 4).add (hSk 0))))).congr
      (fun n => by push_cast; ring)
  have hRHS : Summable (fun n : ℕ =>
      ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 4) * r ^ n) :=
    ((((hSk 4).add ((hSk 3).mul_left 10)).add
        (((hSk 2).mul_left 35).add (((hSk 1).mul_left 50).add ((hSk 0).mul_left 24))))).congr
      (fun n => by push_cast; ring)
  have hpoint : ∀ n : ℕ, ((n : ℝ) + 1) ^ 4 * r ^ n ≤
      ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 4) * r ^ n :=
    fun n => mul_le_mul_of_nonneg_right
      (by nlinarith [Nat.cast_nonneg (α := ℝ) n]) (pow_nonneg hr0 n)
  have hrhs_eq : ∑' n : ℕ,
      ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 4) * r ^ n =
      24 / (1 - r) ^ 5 := by
    have hgen := tsum_choose_mul_geometric_of_norm_lt_one 4 hr_norm
    simp_rw [show ∀ n : ℕ,
        ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 4) * r ^ n =
        24 * (((n + 4).choose 4 : ℝ) * r ^ n) from fun n => by
      have : ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 4) =
          (24 : ℝ) * ((n + 4).choose 4 : ℝ) := by exact_mod_cast (choose_four_val n).symm
      linarith [show ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 4) * r ^ n =
          (24 : ℝ) * ((n + 4).choose 4 : ℝ) * r ^ n from by rw [this]]
      ]
    rw [tsum_mul_left (a := (24 : ℝ)), hgen]; ring
  calc ∑' n : ℕ, ((n : ℝ) + 1) ^ 4 * r ^ n
      ≤ ∑' n : ℕ,
          ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 4) * r ^ n :=
        tsum_le_tsum hpoint hLHS hRHS
    _ = 24 / (1 - r) ^ 5 := hrhs_eq

-- ── Sigma equivalence (for strip decomposition) ───────────────────────────────

private noncomputable def weight_sigma_equiv :
    (Σ k : ℕ, {w : Weight // ⌊casimir_su3 w⌋₊ = k}) ≃ Weight where
  toFun p := p.2.val
  invFun w := ⟨⌊casimir_su3 w⌋₊, ⟨w, rfl⟩⟩
  left_inv := by
    rintro ⟨k, ⟨w, hw⟩⟩
    simp only []
    subst hw; rfl
  right_inv := fun _ => rfl

-- ── Main theorem (Gap 1 + Gap 2 CLOSED) ──────────────────────────────────────

/-- **Wall 256.2b UPPER — heat-trace upper bound from the Weyl law (gaps closed).**

    Given N*(Λ) ≤ C₂·Λ⁴ eventually, K(t) ≤ 386·C₂/t⁴ for all small t > 0.

    HEAD (unchanged): level-set sum ≤ N*(⌊1/t⌋₊) ≤ C₂/t⁴.

    TAIL (Gap 1 + Gap 2 CLOSED):
      tail ≤ ∑_w dim²·r^⌊cas⌋₊                           [quantization]
           = ∑_k strip_k·rᵏ                               [sigma decomp]
           = (1−r)·∑_k ps(k+1)·rᵏ                        [Abel: ps = partial sums]
           ≤ (1−r)·(C₂/t⁴·(1−r)⁻¹ + 24C₂/(1−r)⁵)        [ps(k+1)≤N*(k+1), Weyl+polylog]
           = C₂/t⁴ + 24C₂/(1−r)⁴ ≤ C₂/t⁴ + 384C₂/t⁴    [(1−r)⁴≥(t/2)⁴]
           = 385C₂/t⁴

    HONEST CAVEAT: N*(Λ) ≤ C₂·Λ⁴ is an OPEN input (SU(3) rep-theory, absent
    from mathlib v4.12.0). YM Surface #1: OPEN. No mass-gap claim.

    STATUS: SCAFFOLD — NOT a brick. -/
set_option maxHeartbeats 1600000 in
theorem heat_trace_su3_upper_bound :
    (∃ C₂ > (0 : ℝ), ∀ᶠ Λ : ℝ in atTop, N_star Λ ≤ C₂ * Λ ^ 4) →
    (∃ M > (0 : ℝ), ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      heat_trace_su3 t ≤ M / t ^ 4) := by
  rintro ⟨C₂, hC₂, hN⟩
  obtain ⟨Λ₀, hΛ₀⟩ := Filter.eventually_atTop.mp hN
  let Λ₁ : ℝ := max Λ₀ 1
  have hΛ₁_pos : (0 : ℝ) < Λ₁ := by
    have : (1 : ℝ) ≤ Λ₁ := le_max_right _ _; linarith
  have hΛ₁_Λ₀ : Λ₀ ≤ Λ₁ := le_max_left _ _
  -- Witness M = 386·C₂
  refine ⟨386 * C₂, mul_pos (by norm_num) hC₂, ?_⟩
  have hfilter : Set.Ioo (0 : ℝ) (1 / Λ₁) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    Ioo_mem_nhdsWithin_Ioi ⟨le_refl 0, div_pos one_pos hΛ₁_pos⟩
  filter_upwards [hfilter] with t ht
  obtain ⟨tpos, tsmall⟩ := ht
  have hΛ : Λ₁ ≤ 1 / t := by
    rw [le_div_iff₀ tpos]; linarith [(lt_div_iff hΛ₁_pos).mp tsmall, mul_comm t Λ₁]
  -- Basic r = exp(-t) properties
  set r := exp (-t) with hr_def
  have hr0 : 0 ≤ r := (exp_pos _).le
  have hr1 : r < 1 := by rw [hr_def, exp_lt_one_iff]; linarith
  have h_one_sub : t / 2 ≤ 1 - r := by
    have h_abs : |(-t : ℝ)| ≤ 1 := by rw [abs_neg, abs_of_pos tpos]; linarith
    have h := Real.exp_bound (n := 2) h_abs (by norm_num)
    simp [Finset.sum_range_succ, Nat.factorial] at h
    have hbd := (abs_le.mp h).2
    rw [← hr_def] at hbd
    have h3t : t ^ 2 * (3 / (2 * 2)) ≤ t / 2 := by
      have : t ^ 2 * (3 / (2 * 2) : ℝ) = 3 / 4 * t ^ 2 := by ring
      rw [this]; nlinarith [mul_nonneg tpos.le (show (0 : ℝ) ≤ 1 / 2 - 3 / 4 * t by linarith)]
    linarith [hbd, h3t]
  have h1r_pos : 0 < 1 - r := by linarith
  have h_denom : t ^ 4 / 16 ≤ (1 - r) ^ 4 := by
    have hpos : 0 < t / 2 := by linarith
    have h4 := pow_le_pow_left hpos.le h_one_sub 4
    nlinarith [pow_pos hpos 4, h4]
  have hr_k : ∀ k : ℕ, r ^ k = exp (-t * (k : ℝ)) := fun k => by
    rw [hr_def, ← Real.exp_nat_mul (-t) k]; congr 1; ring
  -- ── Weyl bound at 1/t ──────────────────────────────────────────────────────
  have hNt : (⌊1 / t⌋₊ : ℝ) ≤ 1 / t :=
    Nat.floor_le (le_of_lt (div_pos one_pos tpos))
  have hweyl_at_t : N_star (1 / t) ≤ C₂ / t ^ 4 := by
    have := hΛ₀ (1 / t) (hΛ₁_Λ₀.trans hΛ)
    have : C₂ * (1 / t) ^ 4 = C₂ / t ^ 4 := by ring
    linarith [hΛ₀ (1 / t) (hΛ₁_Λ₀.trans hΛ)]
  -- ── Summability of heat trace ───────────────────────────────────────────────
  have hsumm : Summable (fun w : Weight => (dim_su3 w : ℝ) ^ 2 * exp (-t * casimir_su3 w)) :=
    summable_heat_trace t tpos
  -- ── Level-set finset ────────────────────────────────────────────────────────
  let N := ⌊1 / t⌋₊
  have hS : {w : Weight | casimir_su3 w ≤ (N : ℝ)}.Finite := finite_casimir_le (N : ℝ)
  set s := hS.toFinset with hs_def
  have hs_mem : ∀ w : Weight, w ∈ s ↔ casimir_su3 w ≤ (⌊1 / t⌋₊ : ℝ) := fun w => by
    simp only [hs_def, hS.mem_toFinset, Set.mem_setOf_eq]
  -- ── HEAD BOUND ─────────────────────────────────────────────────────────────
  have hhead : ∑ w in s, (dim_su3 w : ℝ) ^ 2 * exp (-t * casimir_su3 w) ≤ C₂ / t ^ 4 := by
    calc ∑ w in s, (dim_su3 w : ℝ) ^ 2 * exp (-t * casimir_su3 w)
        ≤ ∑ w in s, (dim_su3 w : ℝ) ^ 2 := by
            apply Finset.sum_le_sum; intro w _
            exact mul_le_of_le_one_right (by positivity)
              (Real.exp_le_one_iff.mpr (by nlinarith [casimir_nonneg w, tpos.le]))
      _ = N_star (N : ℝ) := (N_star_eq_sum (N : ℝ)).symm
      _ ≤ N_star (1 / t) := N_star_mono hNt
      _ ≤ C₂ / t ^ 4 := hweyl_at_t
  -- ── TSUM SPLIT ─────────────────────────────────────────────────────────────
  haveI hfin : Fintype ↥(s : Set Weight) := hS.fintype
  have hs_sum : Summable (fun w : ↥(s : Set Weight) =>
      (dim_su3 w.val : ℝ) ^ 2 * exp (-t * casimir_su3 w.val)) :=
    (hasSum_fintype _).summable
  have hsc_sum : Summable (fun w : ↥(s : Set Weight)ᶜ =>
      (dim_su3 w.val : ℝ) ^ 2 * exp (-t * casimir_su3 w.val)) :=
    hsumm.comp_injective Subtype.val Subtype.coe_injective
  have hsplit : heat_trace_su3 t =
      ∑ w in s, (dim_su3 w : ℝ) ^ 2 * exp (-t * casimir_su3 w) +
      ∑' w : ↥(s : Set Weight)ᶜ, (dim_su3 w.val : ℝ) ^ 2 * exp (-t * casimir_su3 w.val) := by
    unfold heat_trace_su3
    rw [← Finset.tsum_subtype' s (fun w => (dim_su3 w : ℝ) ^ 2 * exp (-t * casimir_su3 w))]
    exact (tsum_add_tsum_compl hs_sum hsc_sum).symm
  -- ── TAIL BOUND (Gap 1 + Gap 2 CLOSED) ──────────────────────────────────────
  -- Step T1: Quantize the tail: exp(-t·cas) ≤ r^⌊cas⌋₊
  have hQsumm_sc : Summable (fun w : ↥(s : Set Weight)ᶜ =>
      (dim_su3 w.val : ℝ) ^ 2 * r ^ ⌊casimir_su3 w.val⌋₊) := by
    apply Summable.of_norm_bounded
      (fun w : ↥(s : Set Weight)ᶜ =>
        exp t * ((dim_su3 w.val : ℝ) ^ 2 * exp (-t * casimir_su3 w.val)))
    · exact Summable.mul_left (exp t) hsc_sum
    · intro ⟨w, _⟩
      rw [Real.norm_of_nonneg (by positivity)]
      have hstep : r ^ ⌊casimir_su3 w⌋₊ ≤ rexp t * rexp (-t * casimir_su3 w) := by
        rw [hr_k ⌊casimir_su3 w⌋₊, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hlt := Nat.lt_floor_add_one (casimir_su3 w)
        nlinarith [Nat.cast_nonneg (α := ℝ) ⌊casimir_su3 w⌋₊, tpos.le]
      calc (dim_su3 w : ℝ) ^ 2 * r ^ ⌊casimir_su3 w⌋₊
          ≤ (dim_su3 w : ℝ) ^ 2 * (rexp t * rexp (-t * casimir_su3 w)) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = rexp t * ((dim_su3 w : ℝ) ^ 2 * rexp (-t * casimir_su3 w)) := by ring
  have hTQ : ∑' w : ↥(s : Set Weight)ᶜ,
      (dim_su3 w.val : ℝ) ^ 2 * exp (-t * casimir_su3 w.val) ≤
      ∑' w : ↥(s : Set Weight)ᶜ, (dim_su3 w.val : ℝ) ^ 2 * r ^ ⌊casimir_su3 w.val⌋₊ := by
    apply tsum_le_tsum _ hsc_sum hQsumm_sc
    intro ⟨w, _⟩
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [hr_k ⌊casimir_su3 w⌋₊]; apply Real.exp_le_exp.mpr
    have hnn : 0 ≤ casimir_su3 w := casimir_nonneg w
    nlinarith [Nat.floor_le hnn, tpos.le]
  -- Step T2: Quantized full heat trace (summable)
  have hQsumm : Summable (fun w : Weight => (dim_su3 w : ℝ) ^ 2 * r ^ ⌊casimir_su3 w⌋₊) := by
    apply Summable.of_norm_bounded
      (fun w : Weight => exp t * ((dim_su3 w : ℝ) ^ 2 * exp (-t * casimir_su3 w)))
    · exact Summable.mul_left (exp t) hsumm
    · intro w
      rw [Real.norm_of_nonneg (by positivity)]
      have hstep : r ^ ⌊casimir_su3 w⌋₊ ≤ rexp t * rexp (-t * casimir_su3 w) := by
        rw [hr_k ⌊casimir_su3 w⌋₊, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [Nat.lt_floor_add_one (casimir_su3 w),
                   Nat.cast_nonneg (α := ℝ) ⌊casimir_su3 w⌋₊, tpos.le]
      calc (dim_su3 w : ℝ) ^ 2 * r ^ ⌊casimir_su3 w⌋₊
          ≤ (dim_su3 w : ℝ) ^ 2 * (rexp t * rexp (-t * casimir_su3 w)) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = rexp t * ((dim_su3 w : ℝ) ^ 2 * rexp (-t * casimir_su3 w)) := by ring
  -- Step T3: Lift tail to full quantized sum (tail ≤ full, nonneg)
  have hQs_fin : Summable (fun w : ↥(s : Set Weight) =>
      (dim_su3 w.val : ℝ) ^ 2 * r ^ ⌊casimir_su3 w.val⌋₊) :=
    (hasSum_fintype _).summable
  have hLift : ∑' w : ↥(s : Set Weight)ᶜ,
      (dim_su3 w.val : ℝ) ^ 2 * r ^ ⌊casimir_su3 w.val⌋₊ ≤
      ∑' w : Weight, (dim_su3 w : ℝ) ^ 2 * r ^ ⌊casimir_su3 w⌋₊ := by
    have hfull : ∑' x : ↥(s : Set Weight), (dim_su3 x.val : ℝ) ^ 2 * r ^ ⌊casimir_su3 x.val⌋₊ +
        ∑' x : ↥(s : Set Weight)ᶜ, (dim_su3 x.val : ℝ) ^ 2 * r ^ ⌊casimir_su3 x.val⌋₊ =
        ∑' w : Weight, (dim_su3 w : ℝ) ^ 2 * r ^ ⌊casimir_su3 w⌋₊ :=
      tsum_add_tsum_compl hQs_fin hQsumm_sc
    linarith [tsum_nonneg (f := fun w : ↥(s : Set Weight) =>
      (dim_su3 w.val : ℝ) ^ 2 * r ^ ⌊casimir_su3 w.val⌋₊) (fun w => by positivity)]
  -- Step T4: Sigma decomp: ∑_w dim²·r^⌊cas⌋₊ = ∑_k strip_k·rᵏ
  -- (Following Tauberian.lean Steps D-E verbatim)
  let strip_sum : ℕ → ℝ := fun k =>
    ∑' (w : {w : Weight // ⌊casimir_su3 w⌋₊ = k}), (dim_su3 w.val : ℝ) ^ 2
  have hSigmaEq :
      ∑' w : Weight, (dim_su3 w : ℝ) ^ 2 * r ^ ⌊casimir_su3 w⌋₊ =
      ∑' k : ℕ, strip_sum k * r ^ k := by
    rw [← weight_sigma_equiv.tsum_eq
          (f := fun w : Weight => (dim_su3 w : ℝ) ^ 2 * r ^ ⌊casimir_su3 w⌋₊)]
    change ∑' p : Σ k : ℕ, {w : Weight // ⌊casimir_su3 w⌋₊ = k},
        (dim_su3 p.2.val : ℝ) ^ 2 * r ^ ⌊casimir_su3 p.2.val⌋₊ = _
    have heq_sig : (fun p : Σ k : ℕ, {w : Weight // ⌊casimir_su3 w⌋₊ = k} =>
        (dim_su3 p.2.val : ℝ) ^ 2 * r ^ ⌊casimir_su3 p.2.val⌋₊) =
      fun p => (dim_su3 p.2.val : ℝ) ^ 2 * r ^ p.1 := by
      funext ⟨k, ⟨w, hw⟩⟩; simp only []; exact congrArg _ (congrArg (r ^ ·) hw)
    rw [heq_sig]
    have hSigmaSumm : Summable (fun p : Σ k : ℕ, {w : Weight // ⌊casimir_su3 w⌋₊ = k} =>
        (dim_su3 p.2.val : ℝ) ^ 2 * r ^ p.1) := by
      apply Summable.of_norm_bounded
        (fun p : Σ k : ℕ, {w : Weight // ⌊casimir_su3 w⌋₊ = k} =>
          exp t * ((dim_su3 p.2.val : ℝ) ^ 2 * exp (-t * casimir_su3 p.2.val)))
      · exact Summable.mul_left (exp t) ((weight_sigma_equiv.summable_iff).mpr hsumm)
      · intro ⟨k, ⟨w, hw⟩⟩
        rw [Real.norm_of_nonneg (by positivity)]
        have hlt : casimir_su3 w < (k : ℝ) + 1 := by
          have := Nat.lt_floor_add_one (casimir_su3 w)
          have hcast : (⌊casimir_su3 w⌋₊ : ℝ) = (k : ℝ) := by exact_mod_cast hw
          linarith
        have hnn : 0 ≤ casimir_su3 w := casimir_nonneg w
        have hstep : r ^ k ≤ rexp t * rexp (-t * casimir_su3 w) := by
          rw [hr_k k, ← Real.exp_add]; apply Real.exp_le_exp.mpr
          nlinarith [Nat.cast_nonneg (α := ℝ) k, tpos.le]
        calc (dim_su3 w : ℝ) ^ 2 * r ^ k
            ≤ (dim_su3 w : ℝ) ^ 2 * (rexp t * rexp (-t * casimir_su3 w)) :=
              mul_le_mul_of_nonneg_left hstep (by positivity)
          _ = rexp t * ((dim_su3 w : ℝ) ^ 2 * rexp (-t * casimir_su3 w)) := by ring
    have hInner : ∀ k : ℕ, Summable (fun (w : {w : Weight // ⌊casimir_su3 w⌋₊ = k}) =>
        (dim_su3 w.val : ℝ) ^ 2 * r ^ k) := fun k => by
      haveI : Fintype {w : Weight // ⌊casimir_su3 w⌋₊ = k} := by
        apply Set.Finite.fintype
        apply (finite_casimir_le ((k : ℝ) + 1)).subset
        intro w (hw : ⌊casimir_su3 w⌋₊ = k)
        show casimir_su3 w ≤ (k : ℝ) + 1
        linarith [Nat.lt_floor_add_one (casimir_su3 w),
          show (⌊casimir_su3 w⌋₊ : ℝ) = (k : ℝ) from by exact_mod_cast hw]
      exact (hasSum_fintype _).summable
    rw [tsum_sigma' hInner hSigmaSumm]
    congr 1; ext k; rw [← tsum_mul_right]
  -- Step T5: Abel summation by parts
  -- Define ps k = Σ_{j<k} strip_sum j  (partial sums)
  let ps : ℕ → ℝ := fun k => (Finset.range k).sum strip_sum
  have hps0 : ps 0 = 0 := Finset.sum_range_zero _
  have hps_diff : ∀ k : ℕ, strip_sum k = ps (k + 1) - ps k := fun k => by
    simp [ps, Finset.sum_range_succ]
  have hss_nn : ∀ k : ℕ, 0 ≤ strip_sum k :=
    fun k => tsum_nonneg (fun w => by positivity)
  have hps_nn : ∀ k : ℕ, 0 ≤ ps k :=
    fun k => Finset.sum_nonneg (fun j _ => hss_nn j)
  have hps_mono : ∀ k : ℕ, ps k ≤ ps (k + 1) := fun k => by
    simp [ps, Finset.sum_range_succ, hss_nn k]
  -- T5a: Finiteness of each strip
  have hstrip_fin : ∀ j : ℕ, {w : Weight // ⌊casimir_su3 w⌋₊ = j}.Finite := fun j =>
    (finite_casimir_le ((j : ℝ) + 1)).subset fun w hw => by
      simp only [Set.mem_setOf_eq] at hw ⊢
      linarith [Nat.lt_floor_add_one (casimir_su3 w),
        show (⌊casimir_su3 w⌋₊ : ℝ) = (j : ℝ) from by exact_mod_cast hw]
  -- T5b: ps(k+1) ≤ N_star(k+1)  [GAP 1 KEY STEP]
  -- Uses: disjoint union of strips 0..k ⊆ {cas ≤ k+1}
  have hps_le_Nstar : ∀ k : ℕ, ps (k + 1) ≤ N_star ↑(k + 1) := fun k => by
    rw [N_star_eq_sum]
    -- Convert each strip_sum j to a Finset sum
    have hstrip_tsum : ∀ j : ℕ,
        strip_sum j = ∑ w in (hstrip_fin j).toFinset, (dim_su3 w : ℝ) ^ 2 := fun j => by
      haveI : Fintype {w : Weight // ⌊casimir_su3 w⌋₊ = j} := (hstrip_fin j).fintype
      simp only [strip_sum]
      rw [tsum_fintype]
      exact Finset.sum_subtype _ (fun w => (hstrip_fin j).mem_toFinset) _
    -- Disjoint strips
    have hstrip_disj :
        Set.PairwiseDisjoint (↑(Finset.range (k + 1)) : Set ℕ)
          (fun j => (hstrip_fin j).toFinset) := fun j₁ _ j₂ _ hne => by
      rw [Finset.disjoint_left]
      intro w hw₁ hw₂
      have h1 : ⌊casimir_su3 w⌋₊ = j₁ := by
        simpa [Set.mem_setOf_eq] using (hstrip_fin j₁).mem_toFinset.mp hw₁
      have h2 : ⌊casimir_su3 w⌋₊ = j₂ := by
        simpa [Set.mem_setOf_eq] using (hstrip_fin j₂).mem_toFinset.mp hw₂
      exact hne (h1.symm.trans h2)
    -- biUnion ⊆ Weyl finset for (k+1)
    have hbiunion_le :
        (Finset.range (k + 1)).biUnion (fun j => (hstrip_fin j).toFinset) ⊆
        (finite_casimir_le ↑(k + 1)).toFinset := by
      intro w hw
      obtain ⟨j, hj, hwj⟩ := Finset.mem_biUnion.mp hw
      apply (finite_casimir_le ↑(k + 1)).mem_toFinset.mpr
      simp only [Set.mem_setOf_eq]
      have hjw : ⌊casimir_su3 w⌋₊ = j := by
        simpa [Set.mem_setOf_eq] using (hstrip_fin j).mem_toFinset.mp hwj
      have hj_lt : j < k + 1 := Finset.mem_range.mp hj
      linarith [Nat.lt_floor_add_one (casimir_su3 w),
        show (⌊casimir_su3 w⌋₊ : ℝ) = (j : ℝ) from by exact_mod_cast hjw,
        show (j : ℝ) + 1 ≤ ↑(k + 1) from by exact_mod_cast hj_lt]
    -- Chain: ps(k+1) = Σ strip_sums = Σ finset sums = biUnion sum ≤ N_star
    calc ps (k + 1)
        = (Finset.range (k + 1)).sum strip_sum := rfl
      _ = (Finset.range (k + 1)).sum
            (fun j => ∑ w in (hstrip_fin j).toFinset, (dim_su3 w : ℝ) ^ 2) := by
            congr 1; ext j; exact hstrip_tsum j
      _ = ∑ w in (Finset.range (k + 1)).biUnion (fun j => (hstrip_fin j).toFinset),
            (dim_su3 w : ℝ) ^ 2 :=
            (Finset.sum_biUnion hstrip_disj).symm
      _ ≤ ∑ w in (finite_casimir_le ↑(k + 1)).toFinset, (dim_su3 w : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hbiunion_le (fun w _ _ => by positivity)
      _ = N_star ↑(k + 1) := (N_star_eq_sum ↑(k + 1)).symm
  -- T5c: Extended Weyl bound for ALL k (inside the filter)
  -- For k+1 ≥ Λ₀: N*(k+1) ≤ C₂*(k+1)⁴  from hΛ₀ directly
  -- For k+1 < Λ₀: N*(k+1) ≤ N*(Λ₀) ≤ C₂*(Λ₀)⁴ ≤ C₂*(1/t)⁴ = C₂/t⁴
  have hWeyl_all : ∀ k : ℕ,
      N_star ↑(k + 1) ≤ C₂ / t ^ 4 + C₂ * (↑(k + 1)) ^ 4 := fun k => by
    rcases le_or_lt Λ₀ ↑(k + 1) with hk | hk
    · -- Case: k+1 ≥ Λ₀; use hΛ₀
      linarith [hΛ₀ ↑(k + 1) hk, div_nonneg hC₂.le (pow_pos tpos 4).le]
    · -- Case: k+1 < Λ₀; use monotonicity + Weyl at Λ₀ + filter bound
      have hNstar_k : N_star ↑(k + 1) ≤ N_star Λ₀ :=
        N_star_mono hk.le
      have hNstar_Λ₀ : N_star Λ₀ ≤ C₂ * Λ₀ ^ 4 := hΛ₀ Λ₀ le_rfl
      have hΛ₀_t : Λ₀ ≤ 1 / t := hΛ₁_Λ₀.trans hΛ
      have hΛ₀4 : C₂ * Λ₀ ^ 4 ≤ C₂ / t ^ 4 := by
        have h4 := pow_le_pow_left (by linarith [hΛ₁_pos]) hΛ₀_t 4
        have : (1 / t) ^ 4 = 1 / t ^ 4 := by ring
        nlinarith [hC₂.le]
      linarith [mul_nonneg hC₂.le (pow_nonneg (Nat.cast_nonneg (α := ℝ) (k + 1)) 4)]
  -- T5d: ps(k+1) ≤ C₂/t⁴ + C₂·(k+1)⁴
  have hps_bound : ∀ k : ℕ,
      ps (k + 1) ≤ C₂ / t ^ 4 + C₂ * (↑(k + 1)) ^ 4 :=
    fun k => (hps_le_Nstar k).trans (hWeyl_all k)
  -- T5e: Summability of ps(k+1)·rᵏ
  have hr_norm : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0]
  have hSk_r : ∀ j : ℕ, Summable (fun k : ℕ => (k : ℝ) ^ j * r ^ k) :=
    fun j => summable_pow_mul_geometric_of_norm_lt_one j hr_norm
  have hgeom_summ : Summable (fun k : ℕ => r ^ k) := summable_geometric_of_lt_one hr0 hr1
  have hpow4_summ : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 4 * r ^ k) :=
    ((((hSk_r 4).add ((hSk_r 3).mul_left 4)).add
        (((hSk_r 2).mul_left 6).add (((hSk_r 1).mul_left 4).add (hSk_r 0))))).congr
      (fun k => by push_cast; ring)
  have hSumT : Summable (fun k : ℕ => ps (k + 1) * r ^ k) := by
    apply Summable.of_norm_bounded
      (fun k : ℕ => (C₂ / t ^ 4 + C₂ * (↑(k + 1)) ^ 4) * r ^ k)
    · exact (hgeom_summ.mul_left (C₂ / t ^ 4)).add
        (hpow4_summ.mul_left C₂ |>.congr (fun k => by ring)) |>.congr (fun k => by ring)
    · intro k
      rw [Real.norm_of_nonneg (mul_nonneg (hps_nn (k + 1)) (pow_nonneg hr0 k))]
      exact mul_le_mul_of_nonneg_right (hps_bound k) (pow_nonneg hr0 k)
  have hSumA : Summable (fun k : ℕ => ps k * r ^ k) := by
    apply Summable.of_norm_bounded
      (fun k : ℕ => (C₂ / t ^ 4 + C₂ * (↑(k + 1)) ^ 4) * r ^ k)
    · exact (hgeom_summ.mul_left (C₂ / t ^ 4)).add
        (hpow4_summ.mul_left C₂ |>.congr (fun k => by ring)) |>.congr (fun k => by ring)
    · intro k
      rw [Real.norm_of_nonneg (mul_nonneg (hps_nn k) (pow_nonneg hr0 k))]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [hps0]
      · exact mul_le_mul_of_nonneg_right
          ((hps_mono (k - 1) |>.trans (hps_bound (k - 1)) |>.trans (by
            congr 1
            have : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk
            simp [this]
            nlinarith [Nat.cast_nonneg (α := ℝ) k])))
          (pow_nonneg hr0 k)
  -- T5f: Abel identity: ∑' k, strip_sum k · rᵏ = (1−r) · T
  -- where T = ∑' k, ps(k+1) · rᵏ
  let T : ℝ := ∑' k : ℕ, ps (k + 1) * r ^ k
  have hAbel : ∑' k : ℕ, strip_sum k * r ^ k = (1 - r) * T := by
    -- strip_sum k = ps(k+1) - ps(k), so (ps(k+1) - ps(k))·rᵏ
    have hstep : ∀ k : ℕ, strip_sum k * r ^ k = ps (k + 1) * r ^ k - ps k * r ^ k :=
      fun k => by rw [hps_diff k]; ring
    simp_rw [hstep]
    -- Split tsum of difference
    rw [tsum_sub hSumT hSumA]
    -- Index shift: ∑' k, ps(k)·rᵏ = ps(0) + r · ∑' k, ps(k+1)·rᵏ
    have hshift : ∑' k : ℕ, ps k * r ^ k = r * T := by
      rw [hSumA.tsum_eq_zero_add]
      simp only [hps0, pow_zero, mul_one, zero_add]
      -- ∑' k, ps(k+1)·r^(k+1) = r · T
      have : ∀ k : ℕ, ps (k + 1) * r ^ (k + 1) = r * (ps (k + 1) * r ^ k) := fun k => by ring
      simp_rw [this]
      exact tsum_mul_left
    rw [hshift]
    ring
  -- T5g: T ≤ C₂/t⁴ · (1−r)⁻¹ + C₂ · 24/(1−r)⁵
  have hT_le : T ≤ C₂ / t ^ 4 * (1 - r)⁻¹ + C₂ * (24 / (1 - r) ^ 5) := by
    apply le_trans (tsum_le_tsum (fun k => mul_le_mul_of_nonneg_right (hps_bound k)
        (pow_nonneg hr0 k)) hSumT
      (((hgeom_summ.mul_left (C₂ / t ^ 4)).add
          (hpow4_summ.mul_left C₂ |>.congr (fun k => by ring)))
        |>.congr (fun k => by ring)))
    rw [tsum_add
      (hgeom_summ.mul_left (C₂ / t ^ 4))
      (hpow4_summ.mul_left C₂ |>.congr (fun k => by ring))]
    apply add_le_add
    · rw [tsum_mul_left]
      have hgeom := tsum_geometric_of_lt_one hr0 hr1
      linarith [mul_nonneg (div_nonneg hC₂.le (pow_pos tpos 4).le) (by linarith : (0 : ℝ) ≤ (1 - r)⁻¹)]
    · rw [show (fun k : ℕ => C₂ * (↑(k + 1)) ^ 4 * r ^ k) =
          (fun k : ℕ => C₂ * (((k : ℝ) + 1) ^ 4 * r ^ k)) from by ext k; ring,
        tsum_mul_left]
      exact mul_le_mul_of_nonneg_left (tsum_pow_four_mul_geometric_le hr0 hr1) hC₂.le
  -- T5h: (1−r)·T ≤ C₂/t⁴ + 384·C₂/t⁴ = 385·C₂/t⁴
  have hTail_le : (1 - r) * T ≤ 385 * C₂ / t ^ 4 := by
    calc (1 - r) * T
        ≤ (1 - r) * (C₂ / t ^ 4 * (1 - r)⁻¹ + C₂ * (24 / (1 - r) ^ 5)) :=
          mul_le_mul_of_nonneg_left hT_le (by linarith)
      _ = C₂ / t ^ 4 + 24 * C₂ / (1 - r) ^ 4 := by
          field_simp
          ring
      _ ≤ C₂ / t ^ 4 + 384 * C₂ / t ^ 4 := by
          apply add_le_add_left
          have h384 : 24 * C₂ / (1 - r) ^ 4 ≤ 384 * C₂ / t ^ 4 := by
            rw [div_le_div_iff (pow_pos h1r_pos 4) (pow_pos tpos 4)]
            nlinarith [h_denom, hC₂.le]
          linarith
      _ = 385 * C₂ / t ^ 4 := by ring
  -- ── COMBINE: K(t) = head + tail ≤ C₂/t⁴ + 385C₂/t⁴ = 386C₂/t⁴ ───────────
  rw [hsplit]
  have htail_final :
      ∑' w : ↥(s : Set Weight)ᶜ, (dim_su3 w.val : ℝ) ^ 2 * exp (-t * casimir_su3 w.val) ≤
      385 * C₂ / t ^ 4 :=
    (hTQ.trans hLift).trans (hSigmaEq ▸ hAbel ▸ hTail_le)
  have h386 : C₂ / t ^ 4 + 385 * C₂ / t ^ 4 = 386 * C₂ / t ^ 4 := by ring
  linarith [hhead, htail_final]

end SU3WeylUpper
