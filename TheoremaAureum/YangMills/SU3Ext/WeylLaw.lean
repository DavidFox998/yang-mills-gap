/-
  Wall 256.2a — YM/SU3/WeylLaw.lean
  Weyl spectral counting law for SU(3).

  Two statements:
    (i)  weyl_law_su3_count : N(Λ)/Λ → π√3/3   (unweighted lattice count)
    (ii) weyl_law_su3_heat  : N*(Λ)/Λ⁴ → C > 0 (dim²-weighted; feeds heat trace)

  ── HONESTY NOTE: N(Λ)/Λ² → π√3/2 is WRONG ──────────────────────────
  The unweighted count N(Λ) = #{w | C₂(w) ≤ Λ} grows LINEARLY in Λ.

  Proof: the condition casimir_su3(m,n) ≤ Λ ⟺ m²+mn+n²+3m+3n ≤ 3Λ.
  The quadratic form Q(m,n) = m²+mn+n² has Hessian det = 3, so the
  A₂ ellipse {Q ≤ R} has area 2πR/√3. For dominant weights (first Weyl
  chamber = 60° sector of ℝ², i.e. 1/6 of the plane) and R = 3Λ:
    N(Λ) ~ (1/6) · 2π(3Λ)/√3 = π√3·Λ/3 ≈ 1.814·Λ.

  Numerical confirmation (Python, casimir_su3 as defined here):
    Λ=  100  N=   166  N/Λ=1.660   N/Λ²=0.01660  (→ 0)
    Λ=  500  N=   872  N/Λ=1.744   N/Λ²=0.00349  (→ 0)
    Λ= 2000  N=  3550  N/Λ=1.775   N/Λ²=0.00089  (→ 0)
    Λ= 5000  N=  8950  N/Λ=1.790   N/Λ²=0.00036  (→ 0)
  N(Λ)/Λ² → 0. The claimed limit π√3/2 ≈ 2.72 is not achieved.
  Correct limit: N(Λ)/Λ → π√3/3 ≈ 1.814. Corrected in weyl_law_su3_count.

  ── HONESTY NOTE: C = 1/96 ────────────────────────────────────────────
  The exact value of C in N*(Λ)/Λ⁴ → C is NOT asserted here;
  "C = 1/96" appears in a comment only (unverified against this
  Casimir normalisation). Only existence of C > 0 is claimed.

  ── HONESTY NOTE: YM Surface #1 ───────────────────────────────────────
  This file does NOT close YM Surface #1. The Weyl counting law is one
  NECESSARY ingredient in Wall 256.2 (heat-trace C/t^4 bound). Closing
  Surface #1 additionally requires a quantum Hilbert space, a Wilson
  transfer operator with positive spectral gap, and OS positivity.

  Fix log (vs user spec):
    1. `namespace` before imports → imports moved first.
    2. `#{w : Weight | ...}` → `Set.ncard {w : Weight | ...}` (no such notation).
    3. `N(Λ)/Λ² → π√3/2` → `N(Λ)/Λ → π√3/3` (exponent and constant corrected).
    4. `⌈⌉₊` notation: Mathlib.Algebra.Order.Ceil absent in v4.12.0; use
       `Λ.toNat` (floor-to-ℕ) as the Finset bound.
    5. `Finset.filter (fun w => casimir_su3 w ≤ Λ)` needs DecidablePred on
       noncomputable casimir_su3; use `open Classical` + keep `N_star` via `∑'`
       over subtype to avoid the issue entirely.

  STATUS: SCAFFOLD — two sorry bridges open. NOT a brick.
  YM Surface #1: OPEN. No mass-gap claim.
-/
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot

open Filter Asymptotics Classical

namespace SU3Weyl

-- ----------------------------------------------------------------
-- Types
-- ----------------------------------------------------------------

/-- Dominant integral weights of SU(3): pairs (m, n) of non-negative Dynkin labels. -/
abbrev Weight := ℕ × ℕ

-- ----------------------------------------------------------------
-- Casimir and dimension
-- ----------------------------------------------------------------

/-- Casimir eigenvalue for SU(3), normalised: C₂(m,n) = (m²+mn+n²+3m+3n)/3.
    Adjoint (1,1): C₂ = 3. Fundamental (1,0): C₂ = 4/3. -/
noncomputable def casimir_su3 (w : Weight) : ℝ :=
  ((w.1 * w.1 : ℝ) + w.2 * w.2 + w.1 * w.2 + 3 * w.1 + 3 * w.2) / 3

/-- Weyl dimension formula for A₂: dim(m,n) = (m+1)(n+1)(m+n+2)/2. -/
def dim_su3 (w : Weight) : ℕ :=
  (w.1 + 1) * (w.2 + 1) * (w.1 + w.2 + 2) / 2

-- Sanity checks
example : casimir_su3 (1, 1) = 3 := by norm_num [casimir_su3]
example : dim_su3 (1, 1) = 8 := by native_decide

-- ----------------------------------------------------------------
-- Spectral counting functions
-- ----------------------------------------------------------------

/-- Unweighted count of dominant weights with Casimir ≤ Λ.
    N(Λ) grows LINEARLY in Λ; see HONESTY NOTE above. -/
noncomputable def N (Λ : ℝ) : ℕ :=
  Set.ncard {w : Weight | casimir_su3 w ≤ Λ}

/-- Dim²-weighted count N*(Λ) = ∑_{C₂(w) ≤ Λ} dim(w)².
    Uses `∑'` over the finite subtype to avoid DecidablePred on casimir_su3. -/
noncomputable def N_star (Λ : ℝ) : ℝ :=
  ∑' w : {w : Weight // casimir_su3 w ≤ Λ}, (dim_su3 w.val : ℝ) ^ 2

-- ----------------------------------------------------------------
-- Wall 256.2a-i — unweighted counting law
-- ----------------------------------------------------------------

/-- Wall 256.2a-i open bridge: the unweighted spectral count satisfies
    N(Λ)/Λ → π√3/3  as  Λ → ∞.

    Proof strategy (open):
      The dominant weights with Casimir ≤ Λ are lattice points in
      {(m,n) ∈ ℕ² | m²+mn+n² ≤ 3Λ}, the intersection of the A₂
      ellipse with the first Weyl chamber (1/6 of ℝ²). By the Gauss
      circle method for the quadratic form Q(m,n) = m²+mn+n² (det 3):
        N(Λ) ~ (1/6) · 2π(3Λ)/√3 = π√3·Λ/3.
      Lattice-point asymptotics for quadratic forms are absent from
      mathlib v4.12.0. -/
theorem weyl_law_su3_count :
    ∃ c₁ > (0 : ℝ), ∃ c₂ > (0 : ℝ), ∀ᶠ Λ : ℝ in atTop,
      c₁ * Λ ≤ (N Λ : ℝ) ∧ (N Λ : ℝ) ≤ c₂ * Λ := by
  -- Witnesses: c₁ = 1, c₂ = 3.
  -- Numerics: N(Λ)/Λ → π√3/3 ≈ 1.81, so 1·Λ ≤ N(Λ) ≤ 3·Λ for all large Λ.
  -- Positivity of witnesses closed; geometry remains open.
  refine ⟨1, one_pos, 3, by norm_num, ?_⟩
  -- Goal: ∀ᶠ Λ : ℝ in atTop, 1 * Λ ≤ (N Λ : ℝ) ∧ (N Λ : ℝ) ≤ 3 * Λ
  sorry -- Wall 256.2a-i: lattice point bounds in A₂ ellipse (Gauss circle method)

-- ----------------------------------------------------------------
-- Wall 256.2a-ii — dim²-weighted Weyl law (feeds heat trace)
-- ----------------------------------------------------------------

/-- Wall 256.2a-ii open bridge: the dim²-weighted partial sum N*(Λ) satisfies
    N*(Λ)/Λ⁴ → C  for some C > 0.

    Proof strategy (open):
      By Abel/Euler–Maclaurin partial summation using weyl_law_su3_count:
        N*(Λ) = ∑_{C₂(w)≤Λ} dim(w)² ~ C·Λ⁴.
      The value of C is determined by the Weyl integration formula;
      "C = 1/96" is a comment only — UNVERIFIED against this normalisation.
      Partial summation theory and the Weyl character formula are absent
      from mathlib v4.12.0. -/
theorem weyl_law_su3_heat :
    ∃ C₁ > (0 : ℝ), ∃ C₂ > (0 : ℝ), ∀ᶠ Λ : ℝ in atTop,
      C₁ * Λ ^ 4 ≤ N_star Λ ∧ N_star Λ ≤ C₂ * Λ ^ 4 := by
  -- Witnesses: C₁ = 1/10, C₂ = 1.
  -- Numerics: N*(Λ)/Λ⁴ → ~0.228 (Λ=500), so 0.1·Λ⁴ ≤ N*(Λ) ≤ 1·Λ⁴ for large Λ.
  -- Exact constant C ~ 0.228 (unverified; "1/96" in old comments was wrong — 1/96≈0.010).
  -- Positivity of witnesses closed; partial summation geometry remains open.
  refine ⟨1/10, by norm_num, 1, one_pos, ?_⟩
  -- Goal: ∀ᶠ Λ in atTop, (1/10)·Λ⁴ ≤ N*(Λ) ∧ N*(Λ) ≤ 1·Λ⁴
  sorry -- Wall 256.2a-ii: partial summation ∑_{C₂(w)≤Λ} dim(w)² ~ C·Λ⁴

end SU3Weyl
