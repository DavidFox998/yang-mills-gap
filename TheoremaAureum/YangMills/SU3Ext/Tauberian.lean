/-
  Wall 256.2b — YM/SU3/Tauberian.lean
  Karamata Tauberian bridge: counting bounds → heat-trace bounds.

  Statement: bilateral Weyl bounds C₁·Λ⁴ ≤ N*(Λ) ≤ C₂·Λ⁴ (Wall 256.2a-ii)
  imply bilateral heat-trace bounds D₁/t⁴ ≤ K(t) ≤ D₂/t⁴ as t → 0⁺.

  ── Sorry count: 4 declarations (6 sorry terms) ──────────────────────────────
    tsum_exp_le_integral    — sorry: statement FALSE for f≡1; needs Stieltjes IBP
    le_tsum_exp_of_antitone — sorry: tsum monotone comparison for tsum/Finset absent
    tauberian_su3           — sorry: uses both helpers above + filter smallness
    tauberian_su3_lower     — 3 internal sorries (all structural gaps, listed below):
      (1) {w | casimir w ≤ 1/t}.Finite  — quadratic growth, provable; needs work
      (2) N_star (1/t) = Finset.sum      — tsum_fintype path; blocked on v4.12.0
      (3) Summable (dim²·exp(-t·C))      — dominated convergence; blocked
  ── No sorry: ────────────────────────────────────────────────────────────────
    exp_one_lt_three        — proved: Real.exp_bound n=4 + abs_le unpack
    exp_neg_one_gt_third    — proved: exp_one_lt_three + one_div_lt_one_div
    tauberian_su3_lower     — all non-sorry steps compile:
      filter construction, Λ₁ ≤ 1/t arithmetic, Weyl bound application,
      exp comparison (gcongr closes automatically), sum_mul, sum_le_tsum
  ─────────────────────────────────────────────────────────────────────────────

  BLOCKING GAPS in mathlib v4.12.0 (tracked for upstream):
    1. `tsum_subtype_le_tsum` for noncomputable index: no olean for relating
       N*(Λ) as ∑'-subtype to a Finset sum for the monotone comparison step.
    2. Abel summation for tsum: `∑ f(n)e^{-tn} ≤ f(0) + t∫ f(⌈x⌉)e^{-tx} dx`
       not in mathlib. No Stieltjes ∫ e^{-tλ} dN*(λ) for monotone N*.
    3. Filter transfer: `tendsto_inv_zero_atTop` IS available (confirmed):
         Tendsto (·⁻¹) (nhdsWithin 0 (Ioi 0)) atTop
       But composing with `hN : ∀ᶠ Λ in atTop, ...` to get
       `∀ᶠ t in nhdsWithin 0 (Ioi 0), P (1/t)` requires manual eventually work
       that depends on gaps 1 and 2 being resolved first.

  Self-contained: `import YM.SU3.WeylLaw` dropped — scaffold files have no
  lake-compiled oleans; all defs inline. `𝓝[>]` notation replaced by
  `nhdsWithin 0 (Set.Ioi 0)` (parse-safe in direct-lean).

  STATUS: SCAFFOLD — NOT a registered brick.
  YM Surface #1: OPEN. No mass-gap claim.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Order.Filter.AtTopBot

open Filter Real Classical MeasureTheory
open scoped Interval

namespace SU3Tauberian

-- ── Local defs (self-contained mirror of WeylLaw.lean) ───────────────────

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

-- ── Auxiliary: exp constants (no sorry) ─────────────────────────────────

/-- exp(1) < 3 via Taylor n=4: |exp 1 - 8/3| ≤ 5/96, so exp 1 ≤ 261/96 < 3. -/
theorem exp_one_lt_three : exp 1 < 3 := by
  have h := Real.exp_bound (x := 1) (n := 4) (by norm_num)
  simp [Finset.sum_range_succ] at h
  norm_num [Nat.factorial] at h
  linarith [(abs_le.mp h).2]

/-- exp(-1) > 1/3: equivalently exp(1) < 3, proved above.
    Correct constant for the lower bound witness: D₁ = C₁/3 ≤ exp(-1)·C₁. -/
theorem exp_neg_one_gt_third : exp (-1 : ℝ) > 1 / 3 := by
  have h3 : exp 1 < 3 := exp_one_lt_three
  have hpos : (0 : ℝ) < exp 1 := exp_pos 1
  rw [show (-1 : ℝ) = -(1 : ℝ) from rfl, Real.exp_neg, gt_iff_lt, ← one_div]
  exact one_div_lt_one_div_of_lt hpos h3

-- ── Tauberian helper lemmas (BLOCKED — sorry) ────────────────────────────

/-- **Abel-type upper bound — STATEMENT IS FALSE AS WRITTEN.**

    The general bound `∑' n, f n * exp(-tn) ≤ f(0) + t·∫ f(⌈x⌉)·exp(-tx) dx`
    FAILS for f ≡ 1 (antitone ✓, nonneg ✓):
      LHS = ∑ exp(-tn) ≈ 1/t → ∞ as t → 0
      RHS = 1 + t·(1/t) = 2   (fixed constant)
    Verified numerically: t=0.1 gives LHS≈10.51 >> RHS=2.00.

    The bound only holds for f with subpolynomial growth accounted on the RHS,
    or when a `1/t`-type prefactor is present. The correct form for the heat
    trace application is the Stieltjes IBP identity
      K(t) = ∫₀^∞ exp(-tΛ) dN*(Λ) ≤ ∫₀^∞ exp(-tΛ) d(C₂Λ⁴) = 24C₂/t⁴
    which requires Stieltjes monotone comparison for dN* vs d(C₂Λ⁴) — absent
    from mathlib v4.12.0.

    Missing tools confirmed absent in v4.12.0:
      • `tsum_eq_zero_add`                   — unknown identifier
      • `Nat.ceil` / `⌈x⌉₊`                 — Algebra.Order.Ceil has no olean
      • `Mathlib.Analysis.SumIntegralComparisons` — import timed out (no olean)

    STATUS: BLOCKED — needs Stieltjes measure / Laplace-transform lemmas. -/
theorem tsum_exp_le_integral {f : ℕ → ℝ} (hf : Antitone f) (hnn : ∀ n, 0 ≤ f n)
    (t : ℝ) (ht : 0 < t) :
    ∑' n : ℕ, f n * exp (-t * n) ≤
      f 0 + t * ∫ x in Set.Ioi (0 : ℝ), f ⌈x⌉₊ * exp (-t * x) := by
  sorry -- Wall 256.2b Lemma A: BLOCKED — statement false for f≡1 at small t;
        -- correct form requires Stieltjes IBP for the specific N*(Λ)~CΛ⁴ growth

/-- **Lower bound version.** For antitone nonneg f, the partial sum up to N
    contributes at least exp(-tN)·f(N)·N to the full tsum.
    Needed for: K(t) ≥ exp(-1)·N*(1/t) ≥ (C₁/3)/t⁴.

    BLOCKED: requires tsum_subtype_le_tsum for noncomputable index.
    Estimated 15 lines. -/
theorem le_tsum_exp_of_antitone {f : ℕ → ℝ} (hf : Antitone f) (hnn : ∀ n, 0 ≤ f n)
    (t : ℝ) (ht : 0 < t) (N : ℕ) :
    exp (-t * N) * f N * N ≤ ∑' n : ℕ, f n * exp (-t * n) := by
  sorry -- Wall 256.2b Lemma B: tsum lower bound (mathlib gap)

-- ── Main theorem (single sorry) ──────────────────────────────────────────

/-- **Wall 256.2b — Tauberian inequality (open bridge).**
    Weyl counting bounds C₁·Λ⁴ ≤ N*(Λ) ≤ C₂·Λ⁴ imply
    heat-trace bounds (C₁/3)/t⁴ ≤ K(t) ≤ 26·C₂/t⁴ as t → 0⁺.

    Witnesses: D₁ = C₁/3 > 0 (exp(-1) > 1/3, proved above);
               D₂ = 26·C₂ > 0 (K(t) ≤ C₂/t⁴ + 24·C₂/t⁴ + margin).

    Proof road-map (blocked on Lemmas A and B above):
      Upper: K(t) = ∫ e^{-tλ} dN*(λ)
               ≤ N*(1/t)/t⁴ + ∫_{1/t}^∞ e^{-tλ} d(C₂λ⁴)
               = C₂/t⁴ + 24C₂/t⁴   (Γ(5) = 24)
               ≤ 26·C₂/t⁴.
      Lower: for t ≤ 1/Λ₀ (filter smallness via tendsto_inv_zero_atTop),
               K(t) ≥ exp(-1)·N*(1/t) ≥ exp(-1)·C₁/t⁴ ≥ (C₁/3)/t⁴.
      Filter: `tendsto_inv_zero_atTop` (confirmed available) gives
               `∀ᶠ Λ in atTop, P Λ → ∀ᶠ t in nhdsWithin 0 (Ioi 0), P (1/t)`
               via `Filter.Tendsto.eventually`.

    STATUS: OPEN — BLOCKED on Lemmas A and B. NOT a brick. -/
theorem tauberian_su3 :
    (∃ C₁ > (0 : ℝ), ∃ C₂ > (0 : ℝ), ∀ᶠ Λ : ℝ in atTop,
      C₁ * Λ ^ 4 ≤ N_star Λ ∧ N_star Λ ≤ C₂ * Λ ^ 4) →
    (∃ D₁ > (0 : ℝ), ∃ D₂ > (0 : ℝ),
      ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        D₁ / t ^ 4 ≤ heat_trace_su3 t ∧ heat_trace_su3 t ≤ D₂ / t ^ 4) := by
  rintro ⟨C₁, hC₁, C₂, hC₂, hN⟩
  -- D₁ = C₁/3 > 0  (uses exp(-1) > 1/3 proved above)
  -- D₂ = 26·C₂ > 0
  refine ⟨C₁ / 3, div_pos hC₁ (by norm_num), 26 * C₂, mul_pos (by norm_num) hC₂, ?_⟩
  -- BLOCKED: full proof needs Lemmas A + B + filter smallness transfer.
  -- Sketch (not yet formalised):
  --   obtain ⟨Λ₀, hΛ₀⟩ := Filter.eventually_atTop.mp hN
  --   have hfilt := tendsto_inv_zero_atTop.eventually hN
  --     -- : ∀ᶠ t in nhdsWithin 0 (Ioi 0), C₁*(1/t)⁴ ≤ N_star (1/t) ∧ ...
  --   filter_upwards [hfilt, eventually_nhdsWithin_of_forall (fun t ht => ht)]
  --     with t ⟨hNt_lo, hNt_hi⟩ ht
  --   exact ⟨lower_bound_from_Lemma_B hNt_lo ht exp_neg_one_gt_third,
  --          upper_bound_from_Lemma_A hNt_hi ht⟩
  sorry -- Wall 256.2b: BLOCKED on tsum_exp_le_integral + le_tsum_exp_of_antitone

-- ── Auxiliary: level sets of casimir are finite ──────────────────────────

/-- **casimir level sets are finite.**
    `casimir_su3 (m,n) = (m²+mn+n²+3m+3n)/3 ≥ m²/3`, so `{w | casimir w ≤ Λ}`
    is contained in `Finset.range N ×ˢ Finset.range N` with `N = ⌊√(3Λ)⌋₊ + 1`. -/
lemma finite_casimir_le (Λ : ℝ) : {w : Weight | casimir_su3 w ≤ Λ}.Finite := by
  let N := ⌊Real.sqrt (3 * Λ)⌋₊ + 1
  apply (Finset.finite_toSet (Finset.range N ×ˢ Finset.range N)).subset
  rintro ⟨m, n⟩ hw
  simp only [Set.mem_setOf_eq, casimir_su3, Prod.fst, Prod.snd] at hw
  simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  -- From (m·m + m·n + n·n + 3·m + 3·n)/3 ≤ Λ, both m² and n² are ≤ 3Λ.
  have hm2 : (m : ℝ) ^ 2 ≤ 3 * Λ := by
    nlinarith [mul_nonneg hm hn, sq_nonneg (n : ℝ), show (m : ℝ) ^ 2 = m * m from by ring]
  have hn2 : (n : ℝ) ^ 2 ≤ 3 * Λ := by
    nlinarith [mul_nonneg hm hn, sq_nonneg (m : ℝ), show (n : ℝ) ^ 2 = n * n from by ring]
  -- m ≤ √(3Λ): rewrite m = √(m²), then use √ monotone.
  have hm_le : (m : ℝ) ≤ Real.sqrt (3 * Λ) := by
    rw [← Real.sqrt_sq hm]; exact Real.sqrt_le_sqrt hm2
  have hn_le : (n : ℝ) ≤ Real.sqrt (3 * Λ) := by
    rw [← Real.sqrt_sq hn]; exact Real.sqrt_le_sqrt hn2
  -- m ≤ ⌊√(3Λ)⌋₊ < N  (Nat.le_floor is one-directional: ↑n ≤ a → n ≤ ⌊a⌋₊).
  have hm_fl : m ≤ ⌊Real.sqrt (3 * Λ)⌋₊ := Nat.le_floor hm_le
  have hn_fl : n ≤ ⌊Real.sqrt (3 * Λ)⌋₊ := Nat.le_floor hn_le
  exact ⟨by omega, by omega⟩

-- ── Auxiliary: N_star ↔ Finset sum (finite level set) ───────────────────

/-- **N_star equals the Finset sum over the finite level set.**
    `N_star Λ = ∑' w : {w // casimir w ≤ Λ}, dim² w` equals
    `∑ w in hS.toFinset, dim² w` for `hS = finite_casimir_le Λ`.
    Bridge: `tsum_fintype` converts the tsum to a Fintype sum, then
    `Finset.sum_nbij` (with `i = Subtype.val`) gives the Finset.sum. -/
lemma N_star_eq_sum (Λ : ℝ) :
    N_star Λ = ∑ w in (finite_casimir_le Λ).toFinset, (dim_su3 w : ℝ) ^ 2 := by
  simp only [N_star]
  set hS := finite_casimir_le Λ
  haveI : Fintype {w : Weight // casimir_su3 w ≤ Λ} := hS.fintype
  rw [tsum_fintype]
  -- Goal: ∑ w : {w//casimir w ≤ Λ}, dim² w.val = ∑ w in hS.toFinset, dim² w
  -- Use Finset.sum_nbij with i = Subtype.val, s = Finset.univ, t = hS.toFinset.
  exact Finset.sum_nbij (·.val)
    -- hi: w.val ∈ hS.toFinset
    (fun w _ => hS.mem_toFinset.mpr w.property)
    -- inj: Subtype.val injective
    (fun a _ b _ h => Subtype.ext h)
    -- surj: every b ∈ hS.toFinset lifts to a subtype element
    (fun b hb =>
      ⟨⟨b, hS.mem_toFinset.mp (Finset.mem_coe.mp hb)⟩,
        Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩)
    -- values: (dim_su3 w.val)² = (dim_su3 w.val)²
    (fun w _ => rfl)

-- ── Auxiliary: dim bound + heat-trace summability (open bridges) ──────────

/-- **Weyl dimension bound.**
    `dim_su3(m,n)² ≤ 27·(casimir_su3(m,n)+1)³`.
    Route: 2·dim ≤ (m+1)(n+1)(m+n+2) via Nat.div_mul_le_self, so
    dim² ≤ a²b²(a+b)²/4 (a=m+1, b=n+1).
    27·(casimir+1)³ = K³ where K = a²+ab+b².
    Algebraic identity: 4K³ − a²b²(a+b)² = 4K²(K−ab) + 4Kab(K−ab) + a²b²(4K−(a+b)²),
    each term ≥ 0 (K ≥ ab and 4K ≥ (a+b)²), so K³ ≥ dim². -/
lemma dim_sq_le_casimir_cubed (w : Weight) :
    (dim_su3 w : ℝ) ^ 2 ≤ 27 * (casimir_su3 w + 1) ^ 3 := by
  rcases w with ⟨m, n⟩
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  -- 2*dim ≤ (m+1)*(n+1)*(m+n+2) via Nat.div_mul_le_self
  have h2 : (dim_su3 (m, n) : ℝ) * 2 ≤ ((m : ℝ) + 1) * ((n : ℝ) + 1) * ((m : ℝ) + n + 2) := by
    have hle : dim_su3 (m, n) * 2 ≤ (m + 1) * (n + 1) * (m + n + 2) := by
      unfold dim_su3; exact Nat.div_mul_le_self _ _
    exact_mod_cast hle
  -- dim² ≤ ((m+1)(n+1)(m+n+2))²/4
  have hdim2 : (dim_su3 (m, n) : ℝ) ^ 2 ≤
      ((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + n + 2) ^ 2 / 4 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (dim_su3 (m, n)),
              sq_nonneg ((dim_su3 (m, n) : ℝ) * 2 - ((m : ℝ) + 1) * ((n : ℝ) + 1) * ((m : ℝ) + n + 2))]
  -- 27*(casimir+1)³ = K³, K = m²+mn+n²+3m+3n+3
  have hrw : 27 * (casimir_su3 (m, n) + 1) ^ 3 =
      ((m : ℝ) ^ 2 + (m : ℝ) * n + (n : ℝ) ^ 2 + 3 * m + 3 * n + 3) ^ 3 := by
    simp only [casimir_su3]; ring
  rw [hrw]
  set K := (m : ℝ) ^ 2 + (m : ℝ) * n + (n : ℝ) ^ 2 + 3 * (m : ℝ) + 3 * (n : ℝ) + 3
  have hKnn : (0 : ℝ) ≤ K := by unfold_let K; positivity
  -- K ≥ (m+1)*(n+1)  (K − (m+1)(n+1) = m²+n²+2m+2n+2 ≥ 0)
  have hK3 : ((m : ℝ) + 1) * ((n : ℝ) + 1) ≤ K := by
    unfold_let K; nlinarith [sq_nonneg ((m : ℝ) - n)]
  -- 4K ≥ (m+n+2)²  (4K − (m+n+2)² = 3m²+2mn+3n²+8m+8n+8 ≥ 0)
  have hK4 : ((m : ℝ) + n + 2) ^ 2 ≤ 4 * K := by
    unfold_let K; nlinarith [sq_nonneg ((m : ℝ) - n), sq_nonneg ((m : ℝ) + n)]
  -- Decomposition (verified by ring):
  -- 4K³ − a²b²(a+b)² = 4K²(K−ab) + 4Kab(K−ab) + a²b²(4K−(a+b)²)
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

-- maxHeartbeats 800000: norm instance resolution for ‖·‖ on ℝ is expensive (isDefEq cost).
set_option maxHeartbeats 800000 in
/-- **Heat trace is summable for t > 0.**
    Route:
    1. dim(m,n) ≤ (m+1)²(n+1)² via 2·dim ≤ (m+1)(n+1)(m+n+2) and m+n+2 ≤ 2(m+1)(n+1);
       so dim² ≤ (m+1)⁴(n+1)⁴.
    2. casimir(m,n) ≥ m+n (m²+mn+n² ≥ 0); exp(-t·C) ≤ exp(-t·m)·exp(-t·n).
    3. Bounding function (m+1)⁴·exp(-t·m)·(n+1)⁴·exp(-t·n) is summable via
       summable_mul_of_summable_norm + summable_pow_mul_geometric_of_norm_lt_one. -/
lemma summable_heat_trace (t : ℝ) (ht : 0 < t) :
    Summable (fun w : Weight => (dim_su3 w : ℝ) ^ 2 * exp (-t * casimir_su3 w)) := by
  have hr : ‖Real.exp (-t)‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_one_iff]; linarith
  -- Summable (fun m => m^k · exp(-t·m)) for every k
  have hSk : ∀ k : ℕ, Summable (fun m : ℕ => (m : ℝ) ^ k * Real.exp (-t * m)) := fun k => by
    have hgeo := summable_pow_mul_geometric_of_norm_lt_one k hr
    -- Real.exp_nat_mul: exp(↑n * x) = exp(x)^n  (nat on the left).
    -- .symm gives exp(x)^n = exp(↑n * x); but we need exp(x)^n = exp(-t * ↑n).
    -- Use congr + mul_comm to close.
    have heq : (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-t) ^ n) =
               (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-t * n)) := by
      ext n; congr 1
      -- exp_nat_mul: exp(↑n * x) = exp(x)^n; ← rewrites exp(x)^n → exp(↑n * x).
      -- Then congr 1; ring closes ↑n * -t = -t * ↑n.
      rw [← Real.exp_nat_mul (-t) n]; congr 1; ring
    rwa [heq] at hgeo
  -- Summable (fun m => (m+1)^4 · exp(-t·m)).
  -- Use Summable.congr: the combined (hSk 4 + 4·hSk 3 + ...) sum equals (m+1)^4·exp pointwise,
  -- proved by `ring` which treats (m:ℝ) and exp(-t*m) as free ℝ-variables.
  have hSf : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ 4 * Real.exp (-t * m)) :=
    (((hSk 4).add ((hSk 3).mul_left 4)).add
      (((hSk 2).mul_left 6).add (((hSk 1).mul_left 4).add (hSk 0)))).congr
    (fun m => by ring)
  -- Apply Summable.of_norm_bounded with f(m)·g(n) = (m+1)⁴·e^{-tm}·(n+1)⁴·e^{-tn}
  apply Summable.of_norm_bounded
    (fun w : ℕ × ℕ => ((w.1 : ℝ) + 1) ^ 4 * Real.exp (-t * w.1) *
                       (((w.2 : ℝ) + 1) ^ 4 * Real.exp (-t * w.2)))
  · -- Summable of the bounding function via product rule.
    -- `apply summable_mul_of_summable_norm` fails (HO-unification for ?f/?g), and
    -- `.congr` causes isDefEq timeout elaborating the norm equality under binders.
    -- Fix: prove norm-summability via `funext` + `rw` (no congr/isDefEq overhead),
    -- then `exact summable_mul_of_summable_norm hfn hfn` infers f from hfn's explicit type.
    have hfn : Summable (fun m : ℕ => ‖((m : ℝ) + 1) ^ 4 * Real.exp (-t * (m : ℝ))‖) := by
      have eq : (fun m : ℕ => ‖((m : ℝ) + 1) ^ 4 * Real.exp (-t * (m : ℝ))‖) =
                fun m : ℕ => ((m : ℝ) + 1) ^ 4 * Real.exp (-t * (m : ℝ)) := by
        funext m
        exact Real.norm_of_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
      rw [eq]; exact hSf
    exact summable_mul_of_summable_norm hfn hfn
  · intro ⟨m, n⟩
    rw [Real.norm_of_nonneg (by positivity)]
    -- dim ≤ (m+1)²(n+1)²
    have hdim : (dim_su3 (m, n) : ℝ) ≤ ((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 := by
      have hle : dim_su3 (m, n) * 2 ≤ (m + 1) * (n + 1) * (m + n + 2) := by
        unfold dim_su3; exact Nat.div_mul_le_self _ _
      have h' : (dim_su3 (m, n) : ℝ) * 2 ≤ ((m : ℝ) + 1) * ((n : ℝ) + 1) * ((m : ℝ) + n + 2) :=
        by exact_mod_cast hle
      nlinarith [Nat.cast_nonneg (α := ℝ) (dim_su3 (m, n)),
                mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (Nat.cast_nonneg (α := ℝ) n)]
    -- dim² ≤ (m+1)⁴(n+1)⁴
    have hdim2 : (dim_su3 (m, n) : ℝ) ^ 2 ≤ ((m : ℝ) + 1) ^ 4 * ((n : ℝ) + 1) ^ 4 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (dim_su3 (m, n)),
                sq_nonneg ((dim_su3 (m, n) : ℝ) - ((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2)]
    -- casimir ≥ m+n  (m²+mn+n² ≥ 0)
    have hcas : (m : ℝ) + n ≤ casimir_su3 (m, n) := by
      simp only [casimir_su3]
      nlinarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) n,
                mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (Nat.cast_nonneg (α := ℝ) n),
                sq_nonneg ((m : ℝ)), sq_nonneg ((n : ℝ))]
    -- exp(-t·casimir) ≤ exp(-t·m)·exp(-t·n)
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

-- ── Lower-bound half (sorry count: 0 in tauberian_su3_lower) ─────────────

/-- **Wall 256.2b — Lower-bound half (standalone).** [SORRY COUNT: 0]
    (Internal sorries moved to named open bridges above.)
    Given the Weyl lower bound `C₁·Λ⁴ ≤ N*(Λ)` eventually, the heat trace
    satisfies `(C₁/3)/t⁴ ≤ K(t)` for small t > 0.

    Proof idea:
      1. Fix Λ₁ = max Λ₀ 1 > 0.  For t ∈ (0, 1/Λ₁) we have Λ₁ ≤ 1/t,
         so N*(1/t) ≥ C₁·(1/t)⁴ = C₁/t⁴ (Weyl bound applied at Λ = 1/t).
      2. Every w with casimir(w) ≤ 1/t satisfies exp(-t·casimir(w)) ≥ exp(-1).
         So K(t) = ∑_w dim²·exp(-t·C(w))
                 ≥ ∑_{casimir≤1/t} dim²·exp(-1)
                 = exp(-1)·N*(1/t) ≥ exp(-1)·C₁/t⁴ ≥ (C₁/3)/t⁴.

    Sorry 1: `{w | casimir w ≤ 1/t}.Finite` — casimir grows quadratically; provable
             via quadratic growth bound on casimir_su3 (finite level sets).
    Sorry 2: `N_star (1/t) = ∑ w in hS.toFinset, dim²` — tsum over a finite subtype
             equals the corresponding Finset.sum; blocked on `tsum_fintype` path.
    Sorry 3: `Summable (fun w => dim² w · exp(-t·casimir w))` — heat trace converges;
             needs explicit decay estimate (dim(w)² grows polynomially, exp decays
             super-polynomially in casimir, so dominated convergence closes it). -/
theorem tauberian_su3_lower :
    (∃ C₁ > (0 : ℝ), ∀ᶠ Λ : ℝ in atTop, C₁ * Λ ^ 4 ≤ N_star Λ) →
    (∃ D₁ > (0 : ℝ), ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      D₁ / t ^ 4 ≤ heat_trace_su3 t) := by
  rintro ⟨C₁, hC₁, hN⟩
  obtain ⟨Λ₀, hΛ₀⟩ := Filter.eventually_atTop.mp hN
  -- Lift to Λ₁ = max Λ₀ 1 to guarantee Λ₁ > 0 for the filter construction.
  let Λ₁ : ℝ := max Λ₀ 1
  have hΛ₁_pos : (0 : ℝ) < Λ₁ := by
    have : (1 : ℝ) ≤ Λ₁ := le_max_right _ _; linarith
  have hΛ₁_Λ₀ : Λ₀ ≤ Λ₁ := le_max_left _ _
  -- Witness: D₁ = C₁/3 > 0  (justified by exp(-1) > 1/3, proved above).
  refine ⟨C₁ / 3, div_pos hC₁ (by norm_num), ?_⟩
  -- Filter: t ∈ (0, 1/Λ₁) lies in nhdsWithin 0 (Ioi 0).
  have hfilter : Set.Ioo (0 : ℝ) (1 / Λ₁) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    Ioo_mem_nhdsWithin_Ioi ⟨le_refl 0, div_pos one_pos hΛ₁_pos⟩
  filter_upwards [hfilter] with t ht
  obtain ⟨tpos, tsmall⟩ := ht
  -- Deduce Λ₁ ≤ 1/t from t < 1/Λ₁ and t,Λ₁ > 0.
  have hΛ : Λ₁ ≤ 1 / t := by
    rw [le_div_iff₀ tpos]
    have h1 : t * Λ₁ < 1 := (lt_div_iff hΛ₁_pos).mp tsmall
    linarith [mul_comm t Λ₁]
  -- Weyl bound at Λ = 1/t: C₁·(1/t)⁴ ≤ N*(1/t).
  have hkey : C₁ * (1 / t) ^ 4 ≤ N_star (1 / t) := hΛ₀ (1 / t) (hΛ₁_Λ₀.trans hΛ)
  -- Rewrite C₁*(1/t)⁴ as C₁/t⁴ for the calc.
  have hC1_bound : C₁ / t ^ 4 ≤ N_star (1 / t) := by linarith [show C₁*(1/t)^4 = C₁/t^4 by ring]
  -- Define the level set S = {w | casimir(w) ≤ 1/t}.
  let S := {w : Weight | casimir_su3 w ≤ 1 / t}
  -- Sorry 1 CLOSED: S is finite (casimir grows quadratically — proved above).
  have hS : S.Finite := finite_casimir_le _
  -- Sorry 2 CLOSED: N_star (1/t) = ∑ over hS.toFinset via N_star_eq_sum.
  have hNstar : N_star (1 / t) = ∑ w in hS.toFinset, (dim_su3 w : ℝ) ^ 2 :=
    N_star_eq_sum (1 / t)
  -- Sorry 3 CLOSED: heat trace is summable via summable_heat_trace.
  have hsumm : Summable (fun w : Weight => (dim_su3 w : ℝ) ^ 2 * exp (-t * casimir_su3 w)) :=
    summable_heat_trace t tpos
  -- exp(-1) * (C₁/t⁴) ≤ K(t): key inequality.
  calc C₁ / 3 / t ^ 4
      -- Step 1: (C₁/3)/t⁴ ≤ exp(-1)·(C₁/t⁴)  since exp(-1) > 1/3 and C₁/t⁴ > 0.
      _ ≤ exp (-1 : ℝ) * (C₁ / t ^ 4) := by
          have hX : 0 < C₁ / t ^ 4 := div_pos hC₁ (pow_pos tpos 4)
          have heq : C₁ / 3 / t ^ 4 = (1 / 3 : ℝ) * (C₁ / t ^ 4) := by ring
          linarith [mul_lt_mul_of_pos_right exp_neg_one_gt_third hX]
      -- Step 2: exp(-1)·(C₁/t⁴) ≤ exp(-1)·N*(1/t)  by Weyl bound.
      _ ≤ exp (-1 : ℝ) * N_star (1 / t) :=
          mul_le_mul_of_nonneg_left hC1_bound (exp_pos (-1)).le
      -- Step 3: replace N* with Finset sum.
      _ = exp (-1 : ℝ) * ∑ w in hS.toFinset, (dim_su3 w : ℝ) ^ 2 := by rw [hNstar]
      -- Step 4: distribute exp(-1) into the sum and commute.
      _ = ∑ w in hS.toFinset, (dim_su3 w : ℝ) ^ 2 * exp (-1 : ℝ) := by
          rw [← Finset.sum_mul, mul_comm]
      -- Step 5: exp(-1) ≤ exp(-t·casimir(w)) for each w in S (since t·casimir(w) ≤ 1).
      _ ≤ ∑ w in hS.toFinset, (dim_su3 w : ℝ) ^ 2 * exp (-t * casimir_su3 w) := by
          apply Finset.sum_le_sum
          intro w hw
          -- gcongr extracts the exp exponents: goal becomes -1 ≤ -t * casimir_su3 w.
          gcongr
          -- hw : w ∈ hS.toFinset, i.e. casimir_su3 w ≤ 1/t.
          have hw' : casimir_su3 w ≤ 1 / t := hS.mem_toFinset.mp hw
          -- Need: -1 ≤ -t * casimir_su3 w  ↔  t * casimir_su3 w ≤ 1.
          have h1 : casimir_su3 w * t ≤ 1 := (le_div_iff₀ tpos).mp hw'
          linarith [mul_comm (casimir_su3 w) t]
      -- Step 6: Finset sum ≤ full tsum = K(t).
      _ ≤ heat_trace_su3 t := by
          unfold heat_trace_su3
          apply sum_le_tsum
          · intro w _; positivity
          · exact hsumm

end SU3Tauberian
