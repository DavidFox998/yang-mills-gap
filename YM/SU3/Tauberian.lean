/-
  Wall 256.2b — YM/SU3/Tauberian.lean  [REWRITE 2026-06-15: 0 sorries]
  Karamata Tauberian bridge: strip density → heat-trace bounds.

  The three previously-sorry theorems are DELETED:
    × tsum_exp_le_integral    (statement was false for f≡1)
    × le_tsum_exp_of_antitone (tsum monotone comparison gap)
    × tauberian_su3           (depended on both)

  New sorry-free additions:
    ✔ choose_three_val            6·C(k+3,3) = (k+1)(k+2)(k+3)
    ✔ tsum_pow_mul_geometric_le   ∑(n+1)³·rⁿ ≤ 6/(1-r)⁴  for r ∈ [0,1)
    ✔ weight_sigma_equiv          (Σ k, {w // ⌊cas w⌋₊=k}) ≃ Weight
    ✔ heat_trace_su3_upper_bound  K(t) ≤ D₂/t⁴ from strip density hstrip
    ✔ heat_trace_su3_asymptotic   bilateral conditional theorem

  The "hstrip" hypothesis
    ∀ k, ∑_{⌊cas w⌋₊=k} dim(w)² ≤ A·(k+1)³
  is taken as an explicit open input; proving it from SU(3) representation theory
  is a separate future task.  It is HONEST: we do not assert it as a theorem.

  Proof chain for heat_trace_su3_upper_bound (t ∈ (0,¼)):
    K(t) ≤ ∑_w dim²·exp(-t·⌊cas⌋₊)          [exp(‐t·⌊·⌋₊) ≥ exp(‐t·cas)]
         = ∑_k strip_sum(k)·exp(-t·k)         [sigma decomp via weight_sigma_equiv]
         ≤ A·∑_k (k+1)³·exp(-t·k)             [hstrip pointwise]
         ≤ A·6/(1-e^{-t})⁴                    [tsum_pow_mul_geometric_le]
         ≤ A·6·16/t⁴ = 96A/t⁴                 [1-e^{-t} ≥ t/2 from exp_bound n=2]

  Sorry count: 0.  YM Surface #1: OPEN.  No mass-gap claim.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

set_option maxHeartbeats 800000

open Filter Real Classical

namespace SU3Tauberian

-- ── Local defs (self-contained mirror of WeylLaw) ────────────────────────────

abbrev Weight := ℕ × ℕ

noncomputable def casimir_su3 (w : Weight) : ℝ :=
  ((w.1 * w.1 : ℝ) + w.2 * w.2 + w.1 * w.2 + 3 * w.1 + 3 * w.2) / 3

def dim_su3 (w : Weight) : ℕ :=
  (w.1 + 1) * (w.2 + 1) * (w.1 + w.2 + 2) / 2

noncomputable def N_star (Λ : ℝ) : ℝ :=
  ∑' w : {w : Weight // casimir_su3 w ≤ Λ}, (dim_su3 w.val : ℝ) ^ 2

/-- K(t) = ∑_{w} dim(w)² · exp(-t · casimir(w)) -/
noncomputable def heat_trace_su3 (t : ℝ) : ℝ :=
  ∑' w : Weight, (dim_su3 w : ℝ) ^ 2 * exp (-t * casimir_su3 w)

-- ── Auxiliary: exp constants (no sorry) ──────────────────────────────────────

/-- exp(1) < 3 via Taylor n=4. -/
theorem exp_one_lt_three : exp 1 < 3 := by
  have h := Real.exp_bound (x := 1) (n := 4) (by norm_num)
  simp [Finset.sum_range_succ] at h
  norm_num [Nat.factorial] at h
  linarith [(abs_le.mp h).2]

/-- exp(-1) > 1/3. -/
theorem exp_neg_one_gt_third : exp (-1 : ℝ) > 1 / 3 := by
  have h3 : exp 1 < 3 := exp_one_lt_three
  have hpos : (0 : ℝ) < exp 1 := exp_pos 1
  rw [show (-1 : ℝ) = -(1 : ℝ) from rfl, Real.exp_neg, gt_iff_lt, ← one_div]
  exact one_div_lt_one_div_of_lt hpos h3

-- ── Choose identity and geometric series bound ────────────────────────────────

/-- 6·C(k+3, 3) = (k+1)(k+2)(k+3). -/
private lemma choose_three_val (k : ℕ) :
    6 * (k + 3).choose 3 = (k + 1) * (k + 2) * (k + 3) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (k + 3) 3
  simp [Nat.descFactorial, Nat.factorial] at h
  linarith [show (k + 3) * (k + 2) * (k + 1) = (k + 1) * (k + 2) * (k + 3) from by ring]

/-- ∑_{n≥0} (n+1)³·rⁿ ≤ 6/(1−r)⁴ for r ∈ [0, 1). -/
private lemma tsum_pow_mul_geometric_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' n : ℕ, ((n : ℝ) + 1) ^ 3 * r ^ n ≤ 6 / (1 - r) ^ 4 := by
  have hr_norm : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0]
  have hSk : ∀ j : ℕ, Summable (fun n : ℕ => (n : ℝ) ^ j * r ^ n) :=
    fun j => summable_pow_mul_geometric_of_norm_lt_one j hr_norm
  -- (n+1)³·rⁿ is summable (expand cubic)
  have hLHS : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 3 * r ^ n) :=
    (((hSk 3).add ((hSk 2).mul_left 3)).add
      (((hSk 1).mul_left 3).add (hSk 0))).congr (fun n => by push_cast; ring)
  -- (n+1)(n+2)(n+3)·rⁿ is summable (also cubic)
  have hRHS : Summable (fun n : ℕ => ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * r ^ n) :=
    (((hSk 3).add ((hSk 2).mul_left 6)).add
      (((hSk 1).mul_left 11).add ((hSk 0).mul_left 6))).congr (fun n => by push_cast; ring)
  -- Pointwise: (n+1)³ ≤ (n+1)(n+2)(n+3) since (n+2)(n+3) ≥ (n+1)²
  have hpoint : ∀ n : ℕ, ((n : ℝ) + 1) ^ 3 * r ^ n ≤
      ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * r ^ n := fun n =>
    mul_le_mul_of_nonneg_right
      (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
      (pow_nonneg hr0 n)
  -- ∑ (n+1)(n+2)(n+3)·rⁿ = 6·∑ C(n+3,3)·rⁿ = 6/(1-r)⁴
  have hrhs_eq : ∑' n : ℕ, ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * r ^ n =
      6 / (1 - r) ^ 4 := by
    have hgen := tsum_choose_mul_geometric_of_norm_lt_one 3 hr_norm
    have heq : ∀ n : ℕ,
        ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * r ^ n =
        6 * ((n + 3).choose 3 : ℝ) * r ^ n := fun n => by
      have h3 : ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) =
          (6 : ℝ) * ((n + 3).choose 3 : ℝ) := by exact_mod_cast (choose_three_val n).symm
      rw [h3]
    simp_rw [heq, show ∀ n : ℕ, (6 : ℝ) * ((n + 3).choose 3 : ℝ) * r ^ n =
        6 * (((n + 3).choose 3 : ℝ) * r ^ n) from fun n => by ring]
    -- ∑' n, 6*(c n * r^n) = 6 * ∑' n, c n * r^n  (tsum_mul_left, explicit a)
    have hfactor : ∑' n : ℕ, (6 : ℝ) * (((n + 3).choose 3 : ℝ) * r ^ n) =
        6 * ∑' n : ℕ, ((n + 3).choose 3 : ℝ) * r ^ n :=
      tsum_mul_left (a := (6 : ℝ))
    rw [hfactor, hgen]; ring
  calc ∑' n : ℕ, ((n : ℝ) + 1) ^ 3 * r ^ n
      ≤ ∑' n : ℕ, ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * r ^ n :=
        tsum_le_tsum hpoint hLHS hRHS
    _ = 6 / (1 - r) ^ 4 := hrhs_eq

-- ── Casimir level sets and N_star ────────────────────────────────────────────

/-- Casimir level sets are finite (casimir grows quadratically). -/
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
  have hm_fl : m ≤ ⌊Real.sqrt (3 * Λ)⌋₊ := Nat.le_floor hm_le
  have hn_fl : n ≤ ⌊Real.sqrt (3 * Λ)⌋₊ := Nat.le_floor hn_le
  exact ⟨by omega, by omega⟩

/-- N_star Λ = Finset sum over the finite level set. -/
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

-- ── Dimension bound and heat-trace summability ────────────────────────────────

/-- dim(m,n)² ≤ 27·(casimir(m,n)+1)³. -/
lemma dim_sq_le_casimir_cubed (w : Weight) :
    (dim_su3 w : ℝ) ^ 2 ≤ 27 * (casimir_su3 w + 1) ^ 3 := by
  rcases w with ⟨m, n⟩
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have h2 : (dim_su3 (m, n) : ℝ) * 2 ≤ ((m : ℝ) + 1) * ((n : ℝ) + 1) * ((m : ℝ) + n + 2) := by
    have hle : dim_su3 (m, n) * 2 ≤ (m + 1) * (n + 1) * (m + n + 2) := by
      unfold dim_su3; exact Nat.div_mul_le_self _ _
    exact_mod_cast hle
  have hdim2 : (dim_su3 (m, n) : ℝ) ^ 2 ≤
      ((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + n + 2) ^ 2 / 4 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (dim_su3 (m, n)),
              sq_nonneg ((dim_su3 (m, n) : ℝ) * 2 - ((m : ℝ) + 1) * ((n : ℝ) + 1) * ((m : ℝ) + n + 2))]
  have hrw : 27 * (casimir_su3 (m, n) + 1) ^ 3 =
      ((m : ℝ) ^ 2 + (m : ℝ) * n + (n : ℝ) ^ 2 + 3 * m + 3 * n + 3) ^ 3 := by
    simp only [casimir_su3]; ring
  rw [hrw]
  set K := (m : ℝ) ^ 2 + (m : ℝ) * n + (n : ℝ) ^ 2 + 3 * (m : ℝ) + 3 * (n : ℝ) + 3
  have hKnn : (0 : ℝ) ≤ K := by unfold_let K; positivity
  have hK3 : ((m : ℝ) + 1) * ((n : ℝ) + 1) ≤ K := by
    unfold_let K; nlinarith [sq_nonneg ((m : ℝ) - n)]
  have hK4 : ((m : ℝ) + n + 2) ^ 2 ≤ 4 * K := by
    unfold_let K; nlinarith [sq_nonneg ((m : ℝ) - n), sq_nonneg ((m : ℝ) + n)]
  have hdecomp : 4 * K ^ 3 - ((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + n + 2) ^ 2 =
      4 * K ^ 2 * (K - ((m : ℝ) + 1) * ((n : ℝ) + 1)) +
      4 * K * ((m : ℝ) + 1) * ((n : ℝ) + 1) * (K - ((m : ℝ) + 1) * ((n : ℝ) + 1)) +
      ((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 * (4 * K - ((m : ℝ) + n + 2) ^ 2) := by ring
  have ht1 : 0 ≤ 4 * K ^ 2 * (K - ((m : ℝ) + 1) * ((n : ℝ) + 1)) :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hKnn 2)) (by linarith [hK3])
  have ht2 : 0 ≤ 4 * K * ((m : ℝ) + 1) * ((n : ℝ) + 1) * (K - ((m : ℝ) + 1) * ((n : ℝ) + 1)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hKnn)
      (by linarith)) (by linarith)) (by linarith [hK3])
  have ht3 : 0 ≤ ((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 * (4 * K - ((m : ℝ) + n + 2) ^ 2) :=
    mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by linarith [hK4])
  linarith

-- maxHeartbeats 800000: norm instance resolution for ‖·‖ on ℝ is expensive.
set_option maxHeartbeats 800000 in
/-- Heat trace is summable for t > 0. -/
lemma summable_heat_trace (t : ℝ) (ht : 0 < t) :
    Summable (fun w : Weight => (dim_su3 w : ℝ) ^ 2 * exp (-t * casimir_su3 w)) := by
  have hr : ‖Real.exp (-t)‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_one_iff]; linarith
  have hSk : ∀ k : ℕ, Summable (fun m : ℕ => (m : ℝ) ^ k * Real.exp (-t * m)) := fun k => by
    have hgeo := summable_pow_mul_geometric_of_norm_lt_one k hr
    have heq : (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-t) ^ n) =
               (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-t * n)) := by
      ext n; congr 1
      rw [← Real.exp_nat_mul (-t) n]; congr 1; ring
    rwa [heq] at hgeo
  have hSf : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ 4 * Real.exp (-t * m)) :=
    (((hSk 4).add ((hSk 3).mul_left 4)).add
      (((hSk 2).mul_left 6).add (((hSk 1).mul_left 4).add (hSk 0)))).congr
    (fun m => by ring)
  apply Summable.of_norm_bounded
    (fun w : ℕ × ℕ => ((w.1 : ℝ) + 1) ^ 4 * Real.exp (-t * w.1) *
                       (((w.2 : ℝ) + 1) ^ 4 * Real.exp (-t * w.2)))
  · have hfn : Summable (fun m : ℕ => ‖((m : ℝ) + 1) ^ 4 * Real.exp (-t * (m : ℝ))‖) := by
      have eq : (fun m : ℕ => ‖((m : ℝ) + 1) ^ 4 * Real.exp (-t * (m : ℝ))‖) =
                fun m : ℕ => ((m : ℝ) + 1) ^ 4 * Real.exp (-t * (m : ℝ)) := by
        funext m
        exact Real.norm_of_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
      rw [eq]; exact hSf
    exact summable_mul_of_summable_norm hfn hfn
  · intro ⟨m, n⟩
    rw [Real.norm_of_nonneg (by positivity)]
    have hdim : (dim_su3 (m, n) : ℝ) ≤ ((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 := by
      have hle : dim_su3 (m, n) * 2 ≤ (m + 1) * (n + 1) * (m + n + 2) := by
        unfold dim_su3; exact Nat.div_mul_le_self _ _
      have h' : (dim_su3 (m, n) : ℝ) * 2 ≤ ((m : ℝ) + 1) * ((n : ℝ) + 1) * ((m : ℝ) + n + 2) :=
        by exact_mod_cast hle
      nlinarith [Nat.cast_nonneg (α := ℝ) (dim_su3 (m, n)),
                mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (Nat.cast_nonneg (α := ℝ) n)]
    have hdim2 : (dim_su3 (m, n) : ℝ) ^ 2 ≤ ((m : ℝ) + 1) ^ 4 * ((n : ℝ) + 1) ^ 4 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (dim_su3 (m, n)),
                sq_nonneg ((dim_su3 (m, n) : ℝ) - ((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2)]
    have hcas : (m : ℝ) + n ≤ casimir_su3 (m, n) := by
      simp only [casimir_su3]
      nlinarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) n,
                mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (Nat.cast_nonneg (α := ℝ) n),
                sq_nonneg ((m : ℝ)), sq_nonneg ((n : ℝ))]
    have hexp : Real.exp (-t * casimir_su3 (m, n)) ≤
                Real.exp (-t * (m : ℝ)) * Real.exp (-t * (n : ℝ)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hcas ht.le]
    calc (dim_su3 (m, n) : ℝ) ^ 2 * Real.exp (-t * casimir_su3 (m, n))
        ≤ ((m : ℝ) + 1) ^ 4 * ((n : ℝ) + 1) ^ 4 * Real.exp (-t * casimir_su3 (m, n)) :=
            mul_le_mul_of_nonneg_right hdim2 (Real.exp_pos _).le
      _ ≤ ((m : ℝ) + 1) ^ 4 * ((n : ℝ) + 1) ^ 4 * (Real.exp (-t * m) * Real.exp (-t * n)) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = ((m : ℝ) + 1) ^ 4 * Real.exp (-t * (m : ℝ)) *
          (((n : ℝ) + 1) ^ 4 * Real.exp (-t * (n : ℝ))) := by ring

-- ── Lower-bound half (0 sorries) ─────────────────────────────────────────────

/-- **Wall 256.2b — Lower bound.**
    Weyl lower bound C₁·Λ⁴ ≤ N*(Λ) implies (C₁/3)/t⁴ ≤ K(t) for small t > 0. -/
theorem tauberian_su3_lower :
    (∃ C₁ > (0 : ℝ), ∀ᶠ Λ : ℝ in atTop, C₁ * Λ ^ 4 ≤ N_star Λ) →
    (∃ D₁ > (0 : ℝ), ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      D₁ / t ^ 4 ≤ heat_trace_su3 t) := by
  rintro ⟨C₁, hC₁, hN⟩
  obtain ⟨Λ₀, hΛ₀⟩ := Filter.eventually_atTop.mp hN
  let Λ₁ : ℝ := max Λ₀ 1
  have hΛ₁_pos : (0 : ℝ) < Λ₁ := by
    have : (1 : ℝ) ≤ Λ₁ := le_max_right _ _; linarith
  have hΛ₁_Λ₀ : Λ₀ ≤ Λ₁ := le_max_left _ _
  refine ⟨C₁ / 3, div_pos hC₁ (by norm_num), ?_⟩
  have hfilter : Set.Ioo (0 : ℝ) (1 / Λ₁) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    Ioo_mem_nhdsWithin_Ioi ⟨le_refl 0, div_pos one_pos hΛ₁_pos⟩
  filter_upwards [hfilter] with t ht
  obtain ⟨tpos, tsmall⟩ := ht
  have hΛ : Λ₁ ≤ 1 / t := by
    rw [le_div_iff₀ tpos]
    have h1 : t * Λ₁ < 1 := (lt_div_iff hΛ₁_pos).mp tsmall
    linarith [mul_comm t Λ₁]
  have hkey : C₁ * (1 / t) ^ 4 ≤ N_star (1 / t) := hΛ₀ (1 / t) (hΛ₁_Λ₀.trans hΛ)
  have hC1_bound : C₁ / t ^ 4 ≤ N_star (1 / t) := by linarith [show C₁*(1/t)^4 = C₁/t^4 by ring]
  let S := {w : Weight | casimir_su3 w ≤ 1 / t}
  have hS : S.Finite := finite_casimir_le _
  have hNstar : N_star (1 / t) = ∑ w in hS.toFinset, (dim_su3 w : ℝ) ^ 2 :=
    N_star_eq_sum (1 / t)
  have hsumm : Summable (fun w : Weight => (dim_su3 w : ℝ) ^ 2 * exp (-t * casimir_su3 w)) :=
    summable_heat_trace t tpos
  calc C₁ / 3 / t ^ 4
      _ ≤ exp (-1 : ℝ) * (C₁ / t ^ 4) := by
          have hX : 0 < C₁ / t ^ 4 := div_pos hC₁ (pow_pos tpos 4)
          have h13 : (1 : ℝ) / 3 * (C₁ / t ^ 4) < exp (-1 : ℝ) * (C₁ / t ^ 4) :=
            mul_lt_mul_of_pos_right exp_neg_one_gt_third hX
          linarith [show C₁ / 3 / t ^ 4 = 1 / 3 * (C₁ / t ^ 4) from by ring]
      _ ≤ exp (-1 : ℝ) * N_star (1 / t) :=
          mul_le_mul_of_nonneg_left hC1_bound (exp_pos (-1)).le
      _ = exp (-1 : ℝ) * ∑ w in hS.toFinset, (dim_su3 w : ℝ) ^ 2 := by rw [hNstar]
      _ = ∑ w in hS.toFinset, (dim_su3 w : ℝ) ^ 2 * exp (-1 : ℝ) := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ ∑ w in hS.toFinset, (dim_su3 w : ℝ) ^ 2 * exp (-t * casimir_su3 w) := by
          apply Finset.sum_le_sum
          intro w hw
          gcongr
          have hw' : casimir_su3 w ≤ 1 / t := hS.mem_toFinset.mp hw
          have h1 : casimir_su3 w * t ≤ 1 := (le_div_iff₀ tpos).mp hw'
          linarith [mul_comm (casimir_su3 w) t]
      _ ≤ heat_trace_su3 t := by
          unfold heat_trace_su3
          apply sum_le_tsum
          · intro w _; positivity
          · exact hsumm

-- ── Sigma equivalence (for strip decomposition) ───────────────────────────────

/-- Equivalence between the sigma type (strip index, weight in strip) and Weight. -/
private noncomputable def weight_sigma_equiv :
    (Σ k : ℕ, {w : Weight // ⌊casimir_su3 w⌋₊ = k}) ≃ Weight where
  toFun p := p.2.val
  invFun w := ⟨⌊casimir_su3 w⌋₊, ⟨w, rfl⟩⟩
  left_inv := by
    rintro ⟨k, ⟨w, hw⟩⟩
    simp only []
    subst hw; rfl
  right_inv := fun _ => rfl

-- ── Upper bound from strip density hypothesis ─────────────────────────────────

/-- **Wall 256.2b — Upper bound (sorry-free, conditional).**

    Given the strip density hypothesis `hstrip` — which asserts that the squared
    dimension sum over each casimir strip `{w | ⌊casimir w⌋₊ = k}` is bounded
    by `A·(k+1)³` — the heat trace satisfies `K(t) ≤ D₂/t⁴` for small t > 0.

    The hypothesis `hstrip` encodes SU(3) rep-theory input that is not proved
    here.  The bound D₂ = 96·A arises from the chain:
      K(t) ≤ A·∑_k (k+1)³·e^{-tk} ≤ A·6/(1-e^{-t})⁴ ≤ 96A/t⁴.

    STATUS: CONDITIONAL — hstrip is an open input.
    YM Surface #1: OPEN. No mass-gap claim. -/
theorem heat_trace_su3_upper_bound
    (hstrip : ∃ A > 0, ∀ k : ℕ,
      ∑' (w : {w : Weight // ⌊casimir_su3 w⌋₊ = k}), (dim_su3 w.val : ℝ) ^ 2 ≤
        A * ((k : ℝ) + 1) ^ 3) :
    ∃ D₂ > (0 : ℝ), ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      heat_trace_su3 t ≤ D₂ / t ^ 4 := by
  obtain ⟨A, hA, hS⟩ := hstrip
  -- Witness D₂ = 96·A
  refine ⟨96 * A, mul_pos (by norm_num) hA, ?_⟩
  -- Work on t ∈ (0, 1/4)
  have hfilt : Set.Ioo (0 : ℝ) (1 / 4) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    Ioo_mem_nhdsWithin_Ioi ⟨le_refl 0, by norm_num⟩
  filter_upwards [hfilt] with t ht
  obtain ⟨ht, ht4⟩ := ht
  -- Set r = exp(-t); establish basic bounds on r
  set r := exp (-t) with hr_def
  have hr0 : 0 ≤ r := (exp_pos _).le
  have hr1 : r < 1 := by rw [hr_def, exp_lt_one_iff]; linarith
  -- Step A: 1 - r ≥ t/2  (exp bound via Real.exp_bound n=2)
  have h_one_sub : t / 2 ≤ 1 - r := by
    have h_abs : |(-t : ℝ)| ≤ 1 := by
      rw [abs_neg, abs_of_pos ht]; linarith
    have h := Real.exp_bound (n := 2) h_abs (by norm_num)
    simp [Finset.sum_range_succ, Nat.factorial] at h
    have hbd := (abs_le.mp h).2
    -- hbd has rexp(-t); rewrite to r (= rexp(-t)) so linarith can close
    rw [← hr_def] at hbd
    -- hbd : r - (1 + -t) ≤ t² * (3/(2*2)); need t² * (3/(2*2)) ≤ t/2
    -- Use same atom form as hbd so linarith can chain them
    have h3t : t ^ 2 * (3 / (2 * 2)) ≤ t / 2 := by
      -- normalize 3/(2*2) then use product witness 0 ≤ t*(1/2 - 3/4*t)
      have hrw : t ^ 2 * (3 / (2 * 2) : ℝ) = 3 / 4 * t ^ 2 := by ring
      rw [hrw]
      nlinarith [mul_nonneg ht.le (show (0 : ℝ) ≤ 1 / 2 - 3 / 4 * t by linarith)]
    linarith [hbd, h3t]
  -- Step B: (1 - r)⁴ ≥ t⁴/16
  have h_denom : t ^ 4 / 16 ≤ (1 - r) ^ 4 := by
    have hpos : 0 < t / 2 := by linarith
    have h4 := pow_le_pow_left hpos.le h_one_sub 4
    nlinarith [pow_pos hpos 4, h4]
  -- Summability of K(t)
  have hKsumm : Summable (fun w : Weight => (dim_su3 w : ℝ) ^ 2 * exp (-t * casimir_su3 w)) :=
    summable_heat_trace t ht
  -- Step C: K(t) ≤ quantized heat trace ∑_w dim²·r^⌊cas⌋₊
  -- First prove r^k = exp(-t·k) for all k
  have hr_k : ∀ k : ℕ, r ^ k = exp (-t * (k : ℝ)) := fun k => by
    rw [hr_def, ← Real.exp_nat_mul (-t) k]; congr 1; ring
  -- Summability of quantized heat trace
  have hQsumm : Summable (fun w : Weight => (dim_su3 w : ℝ) ^ 2 * r ^ ⌊casimir_su3 w⌋₊) := by
    apply Summable.of_norm_bounded
      (fun w : Weight => exp t * ((dim_su3 w : ℝ) ^ 2 * exp (-t * casimir_su3 w)))
    · exact Summable.mul_left (exp t) hKsumm
    · intro w
      rw [Real.norm_of_nonneg (by positivity)]
      -- Goal: dim²·r^⌊cas⌋₊ ≤ exp(t)·(dim²·exp(-t·cas))
      -- Prove r^⌊cas⌋₊ ≤ exp(t)·exp(-t·cas) first, then multiply by dim²
      have hstep : r ^ ⌊casimir_su3 w⌋₊ ≤ rexp t * rexp (-t * casimir_su3 w) := by
        rw [hr_k ⌊casimir_su3 w⌋₊, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hlt := Nat.lt_floor_add_one (casimir_su3 w)
        nlinarith [Nat.cast_nonneg (α := ℝ) ⌊casimir_su3 w⌋₊, ht.le]
      calc (dim_su3 w : ℝ) ^ 2 * r ^ ⌊casimir_su3 w⌋₊
          ≤ (dim_su3 w : ℝ) ^ 2 * (rexp t * rexp (-t * casimir_su3 w)) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = rexp t * ((dim_su3 w : ℝ) ^ 2 * rexp (-t * casimir_su3 w)) := by ring
  -- K(t) ≤ quantized heat trace: pointwise exp(-t·cas) ≤ r^⌊cas⌋₊
  have hKQ : heat_trace_su3 t ≤ ∑' w : Weight, (dim_su3 w : ℝ) ^ 2 * r ^ ⌊casimir_su3 w⌋₊ := by
    unfold heat_trace_su3
    apply tsum_le_tsum _ hKsumm hQsumm
    intro w
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    -- exp(-t·cas) ≤ r^⌊cas⌋₊  since ⌊cas⌋₊ ≤ cas → -t·⌊cas⌋₊ ≥ -t·cas
    rw [hr_k ⌊casimir_su3 w⌋₊]
    apply Real.exp_le_exp.mpr
    -- Goal: -t * cas ≤ -t * ⌊cas⌋₊; since -t < 0 and ⌊cas⌋₊ ≤ cas, multiply neg
    have hnn : 0 ≤ casimir_su3 w := by
      rcases w with ⟨m, n⟩; unfold casimir_su3; positivity
    have hfloor := Nat.floor_le hnn
    nlinarith [ht.le]
  -- Step D: Sigma decomposition
  -- ∑_w dim²·r^⌊cas⌋₊ = ∑_k (∑_{⌊cas⌋₊=k} dim²)·r^k
  -- via weight_sigma_equiv + tsum_sigma'
  have hSigmaEq :
      ∑' w : Weight, (dim_su3 w : ℝ) ^ 2 * r ^ ⌊casimir_su3 w⌋₊ =
      ∑' k : ℕ, (∑' (w : {w : Weight // ⌊casimir_su3 w⌋₊ = k}),
        (dim_su3 w.val : ℝ) ^ 2) * r ^ k := by
    -- Rewrite as sigma sum via weight_sigma_equiv
    rw [← weight_sigma_equiv.tsum_eq
          (f := fun w : Weight => (dim_su3 w : ℝ) ^ 2 * r ^ ⌊casimir_su3 w⌋₊)]
    -- weight_sigma_equiv p = p.2.val definitionally; force the goal to that form
    change ∑' p : Σ k : ℕ, {w : Weight // ⌊casimir_su3 w⌋₊ = k},
        (dim_su3 p.2.val : ℝ) ^ 2 * r ^ ⌊casimir_su3 p.2.val⌋₊ = _
    -- Use p.2.property to rewrite ⌊cas(p.2.val)⌋₊ = p.1
    have heq_sig : (fun p : Σ k : ℕ, {w : Weight // ⌊casimir_su3 w⌋₊ = k} =>
        (dim_su3 p.2.val : ℝ) ^ 2 * r ^ ⌊casimir_su3 p.2.val⌋₊) =
      fun p => (dim_su3 p.2.val : ℝ) ^ 2 * r ^ p.1 := by
      funext ⟨k, ⟨w, hw⟩⟩
      simp only []
      congr 1
      exact congrArg (r ^ ·) hw
    rw [heq_sig]
    -- Summability of sigma-indexed function (for tsum_sigma')
    have hSigmaSumm : Summable (fun p : Σ k : ℕ, {w : Weight // ⌊casimir_su3 w⌋₊ = k} =>
        (dim_su3 p.2.val : ℝ) ^ 2 * r ^ p.1) := by
      apply Summable.of_norm_bounded
        (fun p : Σ k : ℕ, {w : Weight // ⌊casimir_su3 w⌋₊ = k} =>
          exp t * ((dim_su3 p.2.val : ℝ) ^ 2 * exp (-t * casimir_su3 p.2.val)))
      · exact Summable.mul_left (exp t)
            ((weight_sigma_equiv.summable_iff).mpr hKsumm)
      · intro ⟨k, ⟨w, hw⟩⟩
        rw [Real.norm_of_nonneg (by positivity)]
        -- Goal: dim²·r^k ≤ exp(t)·(dim²·exp(-t·cas))
        have hlt : casimir_su3 w < (k : ℝ) + 1 := by
          have hflt := Nat.lt_floor_add_one (casimir_su3 w)
          have hcast : (⌊casimir_su3 w⌋₊ : ℝ) = (k : ℝ) := by exact_mod_cast hw
          linarith
        have hnn : 0 ≤ casimir_su3 w := by
          rcases w with ⟨m, n⟩; unfold casimir_su3; positivity
        have hstep : r ^ k ≤ rexp t * rexp (-t * casimir_su3 w) := by
          rw [hr_k k, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          nlinarith [Nat.cast_nonneg (α := ℝ) k, ht.le]
        calc (dim_su3 w : ℝ) ^ 2 * r ^ k
            ≤ (dim_su3 w : ℝ) ^ 2 * (rexp t * rexp (-t * casimir_su3 w)) :=
              mul_le_mul_of_nonneg_left hstep (by positivity)
          _ = rexp t * ((dim_su3 w : ℝ) ^ 2 * rexp (-t * casimir_su3 w)) := by ring
    -- Each fiber sum is summable (finite type)
    have hInner : ∀ k : ℕ, Summable (fun (w : {w : Weight // ⌊casimir_su3 w⌋₊ = k}) =>
        (dim_su3 w.val : ℝ) ^ 2 * r ^ k) := fun k => by
      haveI : Fintype {w : Weight // ⌊casimir_su3 w⌋₊ = k} := by
        apply Set.Finite.fintype
        apply (finite_casimir_le ((k : ℝ) + 1)).subset
        intro w (hw : ⌊casimir_su3 w⌋₊ = k)
        show casimir_su3 w ≤ (k : ℝ) + 1
        have hflt := Nat.lt_floor_add_one (casimir_su3 w)
        have hcast : (⌊casimir_su3 w⌋₊ : ℝ) = (k : ℝ) := by exact_mod_cast hw
        linarith
      exact (hasSum_fintype _).summable
    -- Apply tsum_sigma' then pull out the constant r^k
    rw [tsum_sigma' hInner hSigmaSumm]
    congr 1; ext k
    rw [← tsum_mul_right]
  -- Step E: bound strip sums by A·(k+1)³
  -- Summability of (k+1)³·r^k
  have hSk_summ : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 3 * r ^ k) := by
    have hr_norm : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0]
    have hSj : ∀ j : ℕ, Summable (fun k : ℕ => (k : ℝ) ^ j * r ^ k) :=
      fun j => summable_pow_mul_geometric_of_norm_lt_one j hr_norm
    exact (((hSj 3).add ((hSj 2).mul_left 3)).add
      (((hSj 1).mul_left 3).add (hSj 0))).congr (fun n => by push_cast; ring)
  -- Summability of strip_sum · r^k (dominated by A·(k+1)³·r^k)
  have hLHS_summ : Summable (fun k : ℕ =>
      (∑' (w : {w : Weight // ⌊casimir_su3 w⌋₊ = k}), (dim_su3 w.val : ℝ) ^ 2) * r ^ k) :=
    Summable.of_norm_bounded (fun k => A * ((k : ℝ) + 1) ^ 3 * r ^ k)
      (hSk_summ.mul_left A |>.congr (fun k => by ring))
      (fun k => by
        rw [Real.norm_of_nonneg
          (mul_nonneg (tsum_nonneg fun w => by positivity) (pow_nonneg hr0 k))]
        exact mul_le_mul_of_nonneg_right (hS k) (pow_nonneg hr0 k))
  -- ∑_k strip_sum·r^k ≤ A·∑_k (k+1)³·r^k
  have hBound :
      ∑' k : ℕ, (∑' (w : {w : Weight // ⌊casimir_su3 w⌋₊ = k}),
        (dim_su3 w.val : ℝ) ^ 2) * r ^ k ≤
      A * ∑' k : ℕ, ((k : ℝ) + 1) ^ 3 * r ^ k := by
    calc ∑' (k : ℕ),
            (∑' (w : {w : Weight // ⌊casimir_su3 w⌋₊ = k}), (dim_su3 w.val : ℝ) ^ 2) * r ^ k
        ≤ ∑' (k : ℕ), A * ((k : ℝ) + 1) ^ 3 * r ^ k :=
          tsum_le_tsum (fun k => mul_le_mul_of_nonneg_right (hS k) (pow_nonneg hr0 k))
            hLHS_summ (hSk_summ.mul_left A |>.congr (fun k => by ring))
      _ = A * ∑' (k : ℕ), ((k : ℝ) + 1) ^ 3 * r ^ k := by
          rw [← tsum_mul_left (a := A) (f := fun k : ℕ => ((k : ℝ) + 1) ^ 3 * r ^ k)]
          congr 1; ext k; ring
  -- Step F: apply tsum_pow_mul_geometric_le
  have hGeom : A * ∑' k : ℕ, ((k : ℝ) + 1) ^ 3 * r ^ k ≤ A * (6 / (1 - r) ^ 4) :=
    mul_le_mul_of_nonneg_left (tsum_pow_mul_geometric_le hr0 hr1) hA.le
  -- Step G: A·6/(1-r)⁴ ≤ 96A/t⁴  from (1-r)⁴ ≥ t⁴/16
  have hFinal : A * (6 / (1 - r) ^ 4) ≤ 96 * A / t ^ 4 := by
    have h1r_pos : 0 < 1 - r := by linarith [h_one_sub]
    -- A*6*t^4 ≤ 96*A*(1-r)^4 from h_denom: t^4/16 ≤ (1-r)^4
    have hnum : A * 6 * t ^ 4 ≤ 96 * A * (1 - r) ^ 4 := by
      nlinarith [h_denom, hA.le]
    calc A * (6 / (1 - r) ^ 4)
        = A * 6 / (1 - r) ^ 4 := by ring
      _ ≤ 96 * A / t ^ 4 :=
          (div_le_div_iff (pow_pos h1r_pos 4) (pow_pos ht 4)).mpr hnum
  -- Combine all steps
  calc heat_trace_su3 t
      ≤ ∑' w : Weight, (dim_su3 w : ℝ) ^ 2 * r ^ ⌊casimir_su3 w⌋₊ := hKQ
    _ = ∑' k : ℕ, (∑' (w : {w : Weight // ⌊casimir_su3 w⌋₊ = k}),
          (dim_su3 w.val : ℝ) ^ 2) * r ^ k := hSigmaEq
    _ ≤ A * ∑' k : ℕ, ((k : ℝ) + 1) ^ 3 * r ^ k := hBound
    _ ≤ A * (6 / (1 - r) ^ 4) := hGeom
    _ ≤ 96 * A / t ^ 4 := hFinal

-- ── Bilateral conditional theorem ────────────────────────────────────────────

/-- **Wall 256.2b — Tauberian bilateral bound (conditional, 0 sorries).**

    Given:
    1. Weyl lower bound:  ∃ C₁>0, ∀ᶠ Λ in atTop, C₁·Λ⁴ ≤ N*(Λ)
    2. Strip density:     ∃ A>0, ∀ k, strip_sum(k) ≤ A·(k+1)³

    Conclusion: bilateral heat-trace bounds
      ∃ D₁>0, ∃ D₂>0, ∀ᶠ t near 0⁺, D₁/t⁴ ≤ K(t) ≤ D₂/t⁴.

    Both hypotheses are OPEN (not proved from SU(3) first principles here).
    YM Surface #1: OPEN.  No mass-gap / μ>0 claim. -/
theorem heat_trace_su3_asymptotic
    (hWeyl : ∃ C₁ > (0 : ℝ), ∀ᶠ Λ : ℝ in atTop, C₁ * Λ ^ 4 ≤ N_star Λ)
    (hstrip : ∃ A > (0 : ℝ), ∀ k : ℕ,
      ∑' (w : {w : Weight // ⌊casimir_su3 w⌋₊ = k}), (dim_su3 w.val : ℝ) ^ 2 ≤
        A * ((k : ℝ) + 1) ^ 3) :
    (∃ D₁ > (0 : ℝ), ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      D₁ / t ^ 4 ≤ heat_trace_su3 t) ∧
    (∃ D₂ > (0 : ℝ), ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      heat_trace_su3 t ≤ D₂ / t ^ 4) :=
  ⟨tauberian_su3_lower hWeyl, heat_trace_su3_upper_bound hstrip⟩

end SU3Tauberian
