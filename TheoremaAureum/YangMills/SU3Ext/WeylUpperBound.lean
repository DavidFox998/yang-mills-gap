/-
  Wall 256.2b UPPER — YM/SU3/WeylUpperBound.lean
  Upper heat-trace bound from the Weyl counting law.

  Statement: If N*(Λ) ≤ C₂·Λ⁴ eventually, then K(t) ≤ 28·C₂/t⁴ for small t > 0.

  Proof structure:
    HEAD (casimir ≤ ⌊1/t⌋₊): K_head(t) ≤ N*(N) ≤ N*(1/t) ≤ C₂/t⁴ — NO sorry.
    TAIL (casimir > ⌊1/t⌋₊): K_tail(t) ≤ 27·C₂/t⁴ — sorry BLOCKED (see below).

  ── TAIL SORRY IS BLOCKED ────────────────────────────────────────────────────────

  Gap 1 — 2D→1D partition (~20 lines):
    The tail ∑'_{w:casimir(w)>N} dim(w)²·exp(−t·casimir(w)) must be related to
    ∑_{k≥N} (N*(k+1)−N*(k))·exp(−t·k) by partitioning Weight=ℕ×ℕ by the level
    sets {w | ⌊casimir(w)⌋₊ = k}.  This uses `tsum_sigma` (available) but requires
    a formal proof that every w with casimir(w)>0 lies in exactly one strip
    {w | k < casimir(w) ≤ k+1}, taking ~20 lines of set reasoning.
    ABSENT: a direct mathlib lemma for this weighted-lattice decomposition.

  Gap 2 — quantitative polylogarithm bound (~20 lines):
    After the partition + Abel summation by parts, the tail is bounded by
      (1−exp(−t)) · C₂ · ∑_{k=0}^∞ (k+1)⁴ · exp(−t·k).
    Closing this to C/t⁴ requires two facts:
      (a) ∑_{k=0}^∞ (k+1)⁴·r^k = (1+11r+11r²+r³)/(1−r)⁵ ≤ 24/(1−r)⁵  (0≤r<1)
      (b) (1−exp(−t)) ≤ t  and  (1−exp(−t))^5 ≥ (t/2)^5  for 0 < t ≤ 1
    giving (1−r)·∑(k+1)⁴·r^k ≤ 24/(1−r)^4 ≤ 24/(t/2)^4 = 384/t^4.
    Neither the generating-function identity (a) nor the lower bound in (b) is a
    ready-made lemma in mathlib v4.12.0.  Closing both takes ~20 additional lines.
    The resulting constant is 769·C₂ (head C₂ + tail 768·C₂), not 28·C₂.
    The comment "15 lines + geom series" in the user's sketch underestimates the work;
    achieving a tight constant ~28·C₂ would additionally require starting from k=N
    and using the r^N decay (another 10 lines).

  The tail sorry has the same character as the three open bridges in Tauberian.lean
  (tsum_exp_le_integral, le_tsum_exp_of_antitone, tauberian_su3).

  ── Fixes to the user's proof sketch ─────────────────────────────────────────────

  1. `import YM.SU3.WeylLaw` dropped — scaffold files have no lake-compiled oleans;
     all defs inlined (same approach as Tauberian.lean).
  2. `heat_trace_su3` defined inline (not in WeylLaw.lean).
  3. `hΛ₀_le` (undefined in sketch) removed; Weyl bound applied at 1/t directly.
  4. `tsum_eq_sum_add_tsum_ite` replaced by `tsum_add_tsum_compl` (additive sibling
     of `@[to_additive] tprod_mul_tprod_compl`) + `Finset.tsum_subtype'`.
  5. `exp_le_one_iff.mpr (by positivity)` replaced by `Real.exp_le_one_of_nonpos`
     with `nlinarith`; `positivity` proves nonnegativity, not ≤ 0.
  6. `N_star_eq_sum` proved locally (was in SU3Tauberian, not SU3Weyl).
  7. `𝓝[>] 0` replaced by `nhdsWithin 0 (Set.Ioi 0)` (parse-safe in direct-lean).

  Self-contained: no imports from YM.SU3.* (no oleans available).
  STATUS: SCAFFOLD — NOT a registered brick.
  YM Surface #1: OPEN. No mass-gap claim.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Order.Filter.AtTopBot

open Filter Real Classical
open scoped BigOperators

namespace SU3WeylUpper

-- ── Self-contained defs (mirror of WeylLaw.lean + Tauberian.lean) ────────────

abbrev Weight := ℕ × ℕ

noncomputable def casimir_su3 (w : Weight) : ℝ :=
  ((w.1 * w.1 : ℝ) + w.2 * w.2 + w.1 * w.2 + 3 * w.1 + 3 * w.2) / 3

def dim_su3 (w : Weight) : ℕ :=
  (w.1 + 1) * (w.2 + 1) * (w.1 + w.2 + 2) / 2

noncomputable def N_star (Λ : ℝ) : ℝ :=
  ∑' w : {w : Weight // casimir_su3 w ≤ Λ}, (dim_su3 w.val : ℝ) ^ 2

/-- K(t) = ∑_{w} dim(w)² · exp(−t · casimir(w)) -/
noncomputable def heat_trace_su3 (t : ℝ) : ℝ :=
  ∑' w : Weight, (dim_su3 w : ℝ) ^ 2 * exp (-t * casimir_su3 w)

-- ── Auxiliary lemmas ──────────────────────────────────────────────────────────

lemma casimir_nonneg (w : Weight) : 0 ≤ casimir_su3 w := by
  simp only [casimir_su3]
  have hm : (0 : ℝ) ≤ w.1 := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ w.2 := Nat.cast_nonneg _
  positivity

/-- Level sets of casimir_su3 are finite (quadratic growth). -/
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

/-- N_star is monotone: Λ ≤ Λ' → N_star Λ ≤ N_star Λ'. -/
lemma N_star_mono {Λ Λ' : ℝ} (h : Λ ≤ Λ') : N_star Λ ≤ N_star Λ' := by
  rw [N_star_eq_sum Λ, N_star_eq_sum Λ']
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro w hw
    apply (finite_casimir_le Λ').mem_toFinset.mpr
    exact ((finite_casimir_le Λ).mem_toFinset.mp hw).trans h
  · intro w _ _; exact sq_nonneg _

/-- Heat trace is summable for t > 0. [Proof identical to SU3Tauberian.summable_heat_trace.] -/
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
      have h' : (dim_su3 (m, n) : ℝ) * 2 ≤
          ((m : ℝ) + 1) * ((n : ℝ) + 1) * ((m : ℝ) + n + 2) := by exact_mod_cast hle
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
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hcas ht.le]
    calc (dim_su3 (m, n) : ℝ) ^ 2 * Real.exp (-t * casimir_su3 (m, n))
        ≤ ((m : ℝ) + 1) ^ 4 * ((n : ℝ) + 1) ^ 4 * Real.exp (-t * casimir_su3 (m, n)) :=
            mul_le_mul_of_nonneg_right hdim2 (Real.exp_pos _).le
      _ ≤ ((m : ℝ) + 1) ^ 4 * ((n : ℝ) + 1) ^ 4 * (Real.exp (-t * m) * Real.exp (-t * n)) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = ((m : ℝ) + 1) ^ 4 * Real.exp (-t * (m : ℝ)) *
          (((n : ℝ) + 1) ^ 4 * Real.exp (-t * (n : ℝ))) := by ring

-- ── Main theorem ─────────────────────────────────────────────────────────────

/-- **Wall 256.2b UPPER — heat-trace upper bound from the Weyl law (open bridge).**

    If N*(Λ) ≤ C₂·Λ⁴ eventually, then K(t) ≤ 28·C₂/t⁴ for all small t > 0.

    HEAD (no sorry): the level-set sum ∑_{casimir≤N} dim²·exp(−t·C) is bounded by
      N*(N) ≤ N*(1/t) ≤ C₂·(1/t)⁴ = C₂/t⁴.

    TAIL (sorry BLOCKED): the complement sum ∑_{casimir>N} dim²·exp(−t·C) ≤ 27·C₂/t⁴
      requires converting the 2D tsum to a 1D Abel sum over ⌊casimir⌋₊ level strips
      (Gap 1, ~20 lines) and then a quantitative polylogarithm bound (Gap 2, ~20 lines).
      See the file header for the full block analysis.

    STATUS: SCAFFOLD — NOT a brick. YM Surface #1: OPEN. -/
theorem heat_trace_su3_upper_bound :
    (∃ C₂ > (0 : ℝ), ∀ᶠ Λ : ℝ in atTop, N_star Λ ≤ C₂ * Λ ^ 4) →
    (∃ M > (0 : ℝ), ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      heat_trace_su3 t ≤ M / t ^ 4) := by
  rintro ⟨C₂, hC₂, hN⟩
  obtain ⟨Λ₀, hΛ₀⟩ := Filter.eventually_atTop.mp hN
  -- Lift threshold to Λ₁ = max Λ₀ 1 to guarantee Λ₁ > 0 for the filter.
  let Λ₁ : ℝ := max Λ₀ 1
  have hΛ₁_pos : (0 : ℝ) < Λ₁ := by
    have : (1 : ℝ) ≤ Λ₁ := le_max_right _ _; linarith
  have hΛ₁_Λ₀ : Λ₀ ≤ Λ₁ := le_max_left _ _
  -- Witness: M = 28·C₂ (head C₂/t⁴ + tail 27·C₂/t⁴).
  refine ⟨28 * C₂, mul_pos (by norm_num) hC₂, ?_⟩
  -- Filter: use t ∈ (0, 1/Λ₁) ⊆ nhdsWithin 0 (Ioi 0).
  have hfilter : Set.Ioo (0 : ℝ) (1 / Λ₁) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    Ioo_mem_nhdsWithin_Ioi ⟨le_refl 0, div_pos one_pos hΛ₁_pos⟩
  filter_upwards [hfilter] with t ht
  obtain ⟨tpos, tsmall⟩ := ht
  -- From t < 1/Λ₁: deduce Λ₁ ≤ 1/t.
  have hΛ : Λ₁ ≤ 1 / t := by
    rw [le_div_iff₀ tpos]
    linarith [(lt_div_iff hΛ₁_pos).mp tsmall, mul_comm t Λ₁]
  -- Weyl bound at 1/t: N_star(1/t) ≤ C₂·(1/t)⁴.
  have hweyl : N_star (1 / t) ≤ C₂ * (1 / t) ^ 4 :=
    hΛ₀ (1 / t) (hΛ₁_Λ₀.trans hΛ)
  -- Rewrite C₂·(1/t)⁴ as C₂/t⁴.
  have hweyl' : N_star (1 / t) ≤ C₂ / t ^ 4 := by
    have : C₂ * (1 / t) ^ 4 = C₂ / t ^ 4 := by ring
    linarith
  -- Summability of the heat trace.
  have hsumm : Summable (fun w : Weight => (dim_su3 w : ℝ) ^ 2 * exp (-t * casimir_su3 w)) :=
    summable_heat_trace t tpos
  -- Level set S = {w | casimir(w) ≤ ⌊1/t⌋₊} is finite.
  let N := ⌊1 / t⌋₊
  have hS : {w : Weight | casimir_su3 w ≤ (N : ℝ)}.Finite := finite_casimir_le (N : ℝ)
  set s := hS.toFinset with hs_def
  -- (N : ℝ) ≤ 1/t, so N_star(N) ≤ N_star(1/t) ≤ C₂/t⁴.
  have hNt : (N : ℝ) ≤ 1 / t := Nat.floor_le (le_of_lt (div_pos one_pos tpos))
  -- ── HEAD BOUND (no sorry) ────────────────────────────────────────────────────
  -- ∑ w in s, dim²·exp(−t·casimir) ≤ N_star(⌊1/t⌋₊) ≤ N_star(1/t) ≤ C₂/t⁴.
  have hhead : ∑ w in s, (dim_su3 w : ℝ) ^ 2 * exp (-t * casimir_su3 w) ≤ C₂ / t ^ 4 := by
    calc ∑ w in s, (dim_su3 w : ℝ) ^ 2 * exp (-t * casimir_su3 w)
        -- Drop exp(−t·casimir) ≤ 1 (since −t·casimir ≤ 0).
        ≤ ∑ w in s, (dim_su3 w : ℝ) ^ 2 := by
            apply Finset.sum_le_sum; intro w _
            exact mul_le_of_le_one_right (by positivity)
              (Real.exp_le_one_iff.mpr
                (by nlinarith [casimir_nonneg w, tpos.le]))
      -- The remaining Finset sum equals N_star(N).
      _ = N_star (N : ℝ) := (N_star_eq_sum (N : ℝ)).symm
      -- N_star is monotone and (N : ℝ) ≤ 1/t.
      _ ≤ N_star (1 / t) := N_star_mono hNt
      -- Apply Weyl bound at 1/t.
      _ ≤ C₂ / t ^ 4 := hweyl'
  -- ── TSUM SPLIT ───────────────────────────────────────────────────────────────
  -- Summability on s (finite) and sᶜ (sub-summable from hsumm).
  haveI hfin : Fintype ↥(s : Set Weight) := hS.fintype
  have hs_sum : Summable (fun w : ↥(s : Set Weight) =>
      (dim_su3 w.val : ℝ) ^ 2 * exp (-t * casimir_su3 w.val)) :=
    (hasSum_fintype _).summable
  have hsc_sum : Summable (fun w : ↥(s : Set Weight)ᶜ =>
      (dim_su3 w.val : ℝ) ^ 2 * exp (-t * casimir_su3 w.val)) :=
    hsumm.comp_injective Subtype.val Subtype.coe_injective
  -- Split: K(t) = (∑ in s) + (∑' in sᶜ).
  -- Uses: Finset.tsum_subtype' + tsum_add_tsum_compl (additive of tprod_mul_tprod_compl).
  have hsplit : heat_trace_su3 t =
      ∑ w in s, (dim_su3 w : ℝ) ^ 2 * exp (-t * casimir_su3 w) +
      ∑' w : ↥(s : Set Weight)ᶜ, (dim_su3 w.val : ℝ) ^ 2 * exp (-t * casimir_su3 w.val) := by
    unfold heat_trace_su3
    rw [← Finset.tsum_subtype' s (fun w => (dim_su3 w : ℝ)^2 * exp (-t * casimir_su3 w))]
    exact (tsum_add_tsum_compl hs_sum hsc_sum).symm
  -- ── TAIL BOUND (sorry — BLOCKED on Gap 1 + Gap 2) ───────────────────────────
  have htail : ∑' w : ↥(s : Set Weight)ᶜ,
      (dim_su3 w.val : ℝ) ^ 2 * exp (-t * casimir_su3 w.val) ≤ 27 * C₂ / t ^ 4 := by
    sorry
    -- BLOCKED — Wall 256.2b UPPER tail: same class as tsum_exp_le_integral sorry.
    --
    -- Proof route (for reference):
    --   Step 1 (Gap 1): Partition ↥(s : Set Weight)ᶜ by ⌊casimir(w)⌋₊ = k.
    --     Use `tsum_sigma` on Σ k : ℕ, {w : Weight // ⌊casimir(w)⌋₊ = k ∧ casimir(w) > N}
    --     to write the tail as ∑_{k≥N} (∑_{strip k} dim²·exp(−t·casimir)).
    --     Bound each strip: ∑_{strip k} dim² ≤ N*(k+1) − N*(k) and exp(−t·casimir) ≤ exp(−t·k).
    --     Thus tail ≤ ∑_{k=N}^∞ (N*(k+1) − N*(k)) · exp(−t·k).
    --   Step 2 (Abel summation by parts): The 1D sum satisfies
    --     ∑_{k=N}^∞ (N*(k+1)−N*(k)) · r^k = (1−r) · ∑_{k=N}^∞ N*(k+1) · r^k + boundary terms.
    --   Step 3 (Gap 2 + Weyl): Using N*(k+1) ≤ C₂·(k+1)⁴ and (1−r) ≤ t:
    --     ≤ t · C₂ · ∑_{k=0}^∞ (k+1)⁴ · exp(−t·k) = t · C₂ · (1+11r+11r²+r³)/(1−r)⁵
    --     ≤ t · C₂ · 24/(1−r)⁵ ≤ t · C₂ · 24/(t/2)⁵ = 768·C₂/t⁴.
    --   So 27 can be replaced by 768; the constant 27 in the theorem statement
    --   requires a tighter analysis starting the geometric sum from k=N (not k=0)
    --   using the r^N = exp(−tN) ~ exp(−1) decay factor, adding another 10 lines.
    --
    -- MISSING IN MATHLIB v4.12.0:
    --   • tsum_sigma with casimir-indexed strips (partition proof ~20 lines)
    --   • Finset.sum_Ico ↔ tsum_sigma equivalence for the 1D Abel sum
    --   • Quantitative polylogarithm: ∑(k+1)⁴·r^k = (1+11r+11r²+r³)/(1−r)^5 (~10 lines)
    --   • Lower bound (1−r)^5 ≥ (t/2)^5 for 0 < t ≤ 1 (~5 lines with norm_num)
  -- ── COMBINE ──────────────────────────────────────────────────────────────────
  rw [hsplit]
  have h28 : C₂ / t ^ 4 + 27 * C₂ / t ^ 4 = 28 * C₂ / t ^ 4 := by ring
  linarith [hhead, htail]

end SU3WeylUpper
