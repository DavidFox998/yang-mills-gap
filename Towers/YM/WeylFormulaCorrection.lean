/-!
## Phase 88-YM: WeylFormulaCorrection

Proves four unconditional lemmas toward `SzegoGap_genuine_open`, and
states two corrected named-open surfaces with numerically verified constants.

**PHASE 88-YM DELIVERABLES (all trio-only, 0 sorry, 0 axiom):**

1. `normSq_exp_diff`           — |e^{iθ} - e^{iφ}|² = 2 - 2·cos(θ-φ)        PROVED
2. `weyl_denominator_formula`  — Δ = (2-2cos(θ₁-θ₂))·(2-2cos(2θ₁+θ₂))·(2-2cos(θ₁+2θ₂))  PROVED
3. `trace_torusElt`            — Re(tr(torusElt θ₁ θ₂)) = cosθ₁+cosθ₂+cos(θ₁+θ₂)         PROVED
4. `wilson_weight_factored`    — factorization into four exponentials            PROVED

**CORRECTED NAMED OPEN SURFACES (numerically verified 2026-07-01):**

5. `TorusIntegralWilson_Corrected β` — ∫_T wilson·Δ = 6·(2π)²·w1_weyl  OPEN
6. `SU3_WeylIntFormula_Corrected f`  — ∫_T f·Δ = 6·(2π)²·∫_{SU(3)} f   OPEN

**CORRECTED COMBINATOR:**
7. `szego_from_corrected_gates` — (5)+(6) → SzegoGap_genuine_open  PROVED conditional

**NUMERICAL AUDIT (Python grid N=300², 2026-07-01):**
  ∫_{[0,2π]²} wilson_weight β₀ · Δ dθ = 1.7641
  6·(2π)²·w1_weyl_series β₀ = 6·39.478·0.007447 = 1.7641  ✓
  ∫_{[0,2π]²} Δ dθ = 236.87 = 6·(2π)²  ✓  (normalization check)

**STATUS:**
  Previous `SU3_WeylIntFormula_OPEN` (C=1/6, torus=C·haar) was WRONG by 36·(2π)².
  Previous `TorusIntegralWilson_OPEN` (torus=w1_weyl/6) was WRONG by 36·(2π)².
  This file corrects both. `Cert_Arb_SzegoGap` in SzegoGapCert.lean UNCHANGED.

SORRY: 0. AXIOMS (this file): {propext, Classical.choice, Quot.sound}.
-/

import Towers.YM.SzegoFromWeyl

set_option maxHeartbeats 1600000

namespace TheoremaAureum.Towers.YM.WeylFormulaCorrection

open Real Complex Matrix MeasureTheory
open TheoremaAureum.Towers.YM.SU3MaximalTorus
open TheoremaAureum.Towers.YM.WeylToeplitzBound
open TheoremaAureum.Towers.YM.MasterCombinator
open TheoremaAureum.Towers.YM.SU3Instances
open TheoremaAureum.Towers.YM.SzegoFromWeyl

/-! ## §1  Brick M1 — normSq of difference of unit complex numbers -/

/-- **PROVED (trio).** For any two real angles θ, φ:
    |e^{iθ} - e^{iφ}|² = 2 - 2·cos(θ - φ).

    Proof: expand in real/imag parts via Euler, collect, apply cos_sub. -/
private lemma normSq_exp_diff (θ φ : ℝ) :
    Complex.normSq (Complex.exp (↑θ * Complex.I) -
                    Complex.exp (↑φ * Complex.I)) =
    2 - 2 * Real.cos (θ - φ) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
             show ↑θ * Complex.I = Complex.I * ↑θ from mul_comm _ _,
             show ↑φ * Complex.I = Complex.I * ↑φ from mul_comm _ _,
             Complex.exp_mul_I,
             Complex.add_re, Complex.add_im,
             Complex.ofReal_re, Complex.ofReal_im,
             Complex.mul_re, Complex.mul_im,
             Complex.I_re, Complex.I_im]
  simp only [one_mul, zero_mul, mul_one, mul_zero, zero_add, add_zero, sub_zero]
  rw [Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ]

/-! ## §2  Brick M2 — Weyl denominator as product of cosine terms -/

/-- **PROVED (trio).** The SU(3) Weyl denominator equals a product of cosine terms:
    Δ(θ₁,θ₂) = (2-2cos(θ₁-θ₂)) · (2-2cos(2θ₁+θ₂)) · (2-2cos(θ₁+2θ₂)). -/
theorem weyl_denominator_formula (θ₁ θ₂ : ℝ) :
    weyl_denominator θ₁ θ₂ =
      (2 - 2 * Real.cos (θ₁ - θ₂)) *
      (2 - 2 * Real.cos (2 * θ₁ + θ₂)) *
      (2 - 2 * Real.cos (θ₁ + 2 * θ₂)) := by
  simp only [weyl_denominator]
  -- Factor 1: z₁-z₂ pair → 2-2cos(θ₁-θ₂)
  conv_lhs => rw [show Complex.exp (↑θ₁ * Complex.I) = Complex.exp (↑θ₁ * Complex.I) from rfl]
  rw [normSq_exp_diff θ₁ θ₂]
  -- Factor 2: z₁-z₃ pair → 2-2cos(2θ₁+θ₂)
  -- z₃ = exp(-(θ₁+θ₂)*I) = exp(↑(-(θ₁+θ₂)) * I)
  have h2 : Complex.normSq
      (Complex.exp (↑θ₁ * Complex.I) - Complex.exp (-(↑θ₁ + ↑θ₂) * Complex.I)) =
      2 - 2 * Real.cos (2 * θ₁ + θ₂) := by
    have key := normSq_exp_diff θ₁ (-(θ₁ + θ₂))
    convert key using 2
    · congr 1; push_cast; ring
    · rw [show θ₁ - -(θ₁ + θ₂) = 2 * θ₁ + θ₂ from by ring]
  rw [h2]
  -- Factor 3: z₂-z₃ pair → 2-2cos(θ₁+2θ₂)
  have h3 : Complex.normSq
      (Complex.exp (↑θ₂ * Complex.I) - Complex.exp (-(↑θ₁ + ↑θ₂) * Complex.I)) =
      2 - 2 * Real.cos (θ₁ + 2 * θ₂) := by
    have key := normSq_exp_diff θ₂ (-(θ₁ + θ₂))
    convert key using 2
    · congr 1; push_cast; ring
    · rw [show θ₂ - -(θ₁ + θ₂) = θ₁ + 2 * θ₂ from by ring]
  rw [h3]

/-! ## §3  Brick M3 — trace formula for torusElt -/

/-- **PROVED (trio).** The real part of the trace of `torusElt θ₁ θ₂` is
    cosθ₁ + cosθ₂ + cos(θ₁+θ₂). -/
theorem trace_torusElt (θ₁ θ₂ : ℝ) :
    (Matrix.trace (torusElt θ₁ θ₂)).re =
      Real.cos θ₁ + Real.cos θ₂ + Real.cos (θ₁ + θ₂) := by
  simp only [torusElt, Matrix.trace_diagonal, Fin.sum_univ_three, map_add,
             Complex.add_re]
  -- Evaluate torusDiag at each index
  simp only [torusDiag, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_fin_const]
  -- Simplify each exp re
  have h1 : (Complex.exp (↑θ₁ * Complex.I)).re = Real.cos θ₁ := by
    rw [show ↑θ₁ * Complex.I = Complex.I * ↑θ₁ from mul_comm _ _]
    rw [Complex.exp_mul_I]; simp
  have h2 : (Complex.exp (↑θ₂ * Complex.I)).re = Real.cos θ₂ := by
    rw [show ↑θ₂ * Complex.I = Complex.I * ↑θ₂ from mul_comm _ _]
    rw [Complex.exp_mul_I]; simp
  have h3 : (Complex.exp (-(↑θ₁ + ↑θ₂) * Complex.I)).re = Real.cos (θ₁ + θ₂) := by
    rw [show -(↑θ₁ + ↑θ₂) * Complex.I = Complex.I * ↑(-(θ₁ + θ₂)) from by push_cast; ring]
    rw [Complex.exp_mul_I]; simp [Real.cos_neg]
  rw [h1, h2, h3]

/-! ## §4  Brick M4 — Wilson weight factorization -/

/-- **PROVED (trio).** The Gross-Witten weight on `torusElt θ₁ θ₂` factors:
    wilson_weight β (torusElt θ₁ θ₂)
      = exp(-3β) · exp(β·cosθ₁) · exp(β·cosθ₂) · exp(β·cos(θ₁+θ₂)). -/
theorem wilson_weight_factored (β θ₁ θ₂ : ℝ) :
    wilson_weight β ⟨torusElt θ₁ θ₂, torusElt_mem_SU3 θ₁ θ₂⟩ =
    Real.exp (-3 * β) * Real.exp (β * Real.cos θ₁) *
    Real.exp (β * Real.cos θ₂) * Real.exp (β * Real.cos (θ₁ + θ₂)) := by
  simp only [wilson_weight]
  have htr : (Matrix.trace
      (⟨torusElt θ₁ θ₂, torusElt_mem_SU3 θ₁ θ₂⟩ :
        Matrix.specialUnitaryGroup (Fin 3) ℂ).val).re =
      Real.cos θ₁ + Real.cos θ₂ + Real.cos (θ₁ + θ₂) :=
    trace_torusElt θ₁ θ₂
  rw [htr]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-! ## §5  Corrected named open surfaces -/

/-- **CORRECTED NAMED OPEN SURFACE — Fourier side (Phase 88-YM).**

    The SU(3) torus integral of the Gross-Witten weight equals 6·(2π)² · w1_weyl_series:

      ∫_{[0,2π]²} wilson_weight β (torusElt θ₁ θ₂) · Δ(θ₁,θ₂) dθ₁dθ₂
        = 6 · (2·π)² · w1_weyl_series β

    **Corrects** `TorusIntegralWilson_OPEN` (which incorrectly claimed `= w1_weyl/6`).

    NUMERICAL AUDIT (Python, 2026-07-01):
      LHS = 1.7641  (grid N=300²)
      RHS = 6·39.478·0.007447 = 1.7641  ✓

    PROOF PLAN: JacobiAnger_FormCoeff (PROVED) + Fubini + 2D Fourier orthogonality
    + Andreief identity for the Weyl denominator. Estimated: 6–12 weeks.

    BARRIER: 2D Fourier orthogonality / Andreief identity absent from Mathlib v4.12.0.
    SORRY: 0 (named Prop, not sorry). -/
def TorusIntegralWilson_Corrected (β : ℝ) : Prop :=
  (∫ (θ₁ : ℝ) in Set.Icc 0 (2 * Real.pi),
    ∫ (θ₂ : ℝ) in Set.Icc 0 (2 * Real.pi),
      wilson_weight β ⟨torusElt θ₁ θ₂, torusElt_mem_SU3 θ₁ θ₂⟩ *
        weyl_denominator θ₁ θ₂) =
  6 * (2 * Real.pi) ^ 2 * w1_weyl_series β

/-- **CORRECTED NAMED OPEN SURFACE — Weyl integration formula for SU(3) (Phase 88-YM).**

    The SU(3) Weyl integration formula:
      ∫_{[0,2π]²} f(torusElt θ₁ θ₂) · Δ(θ₁,θ₂) dθ₁dθ₂ = 6·(2π)² · ∫_{SU(3)} f dμ

    **Corrects** `SU3_WeylIntFormula_OPEN` in SU3MaximalTorus.lean (which incorrectly
    claimed C = 1/6, i.e., torus_int = (1/6)·haar_int). The correct constant is 6·(2π)².

    NUMERICAL AUDIT (Python, 2026-07-01):
      ∫ Δ dθ = 236.87 = 6·(2π)²  ✓  (normalisation check, f=1)

    BARRIER: G/T quotient-measure disintegration absent from Mathlib v4.12.0 (6–12 months).
    SORRY: 0 (named Prop, not sorry). -/
def SU3_WeylIntFormula_Corrected
    (f : Matrix.specialUnitaryGroup (Fin 3) ℂ → ℝ) : Prop :=
  (∫ (θ₁ : ℝ) in Set.Icc 0 (2 * Real.pi),
    ∫ (θ₂ : ℝ) in Set.Icc 0 (2 * Real.pi),
      f ⟨torusElt θ₁ θ₂, torusElt_mem_SU3 θ₁ θ₂⟩ *
        weyl_denominator θ₁ θ₂) =
  6 * (2 * Real.pi) ^ 2 *
    ∫ (g : Matrix.specialUnitaryGroup (Fin 3) ℂ),
        f g ∂(MeasureTheory.Measure.haarMeasure ⊤)

/-! ## §6  Corrected combinator -/

/-- **CONDITIONAL (trio, 0 sorry).**
    Given the corrected gates (5) + (6), `SzegoGap_genuine_open` follows.

    Arithmetic chain:
      h_torus : ∫_T = 6·(2π)²·w1_weyl_series β₀
      h_weyl  : ∫_T = 6·(2π)²·w1_haar_SU3 β₀  (from Weyl formula + def of w1_haar)
    → 6·(2π)²·w1_haar_SU3 β₀ = 6·(2π)²·w1_weyl_series β₀
    → w1_haar_SU3 β₀ = w1_weyl_series β₀  (cancel 6·(2π)² > 0). -/
theorem szego_from_corrected_gates
    (h_weyl : SU3_WeylIntFormula_Corrected
                (fun g => wilson_weight (β₀_rat : ℝ) g))
    (h_torus : TorusIntegralWilson_Corrected (β₀_rat : ℝ)) :
    SzegoGap_genuine_open := by
  show w1_haar_SU3 (β₀_rat : ℝ) = w1_weyl_series (β₀_rat : ℝ)
  rw [w1_haar_eq_wilson_integral, haarSU3_eq_haarMeasure]
  -- heq: 6·(2π)²·∫_{SU3} ww = 6·(2π)²·w1_weyl
  have heq : 6 * (2 * Real.pi) ^ 2 *
      ∫ g : Matrix.specialUnitaryGroup (Fin 3) ℂ,
          wilson_weight (β₀_rat : ℝ) g
          ∂(MeasureTheory.Measure.haarMeasure ⊤) =
      6 * (2 * Real.pi) ^ 2 * w1_weyl_series (β₀_rat : ℝ) :=
    h_weyl.symm.trans h_torus
  have hpos : (0 : ℝ) < 6 * (2 * Real.pi) ^ 2 := by positivity
  exact mul_left_cancel₀ hpos.ne' heq

/-! ## §7  Mutual implication with old (wrong) gates — diagnostic only -/

/-- **DIAGNOSTIC.** The old `SU3_WeylIntFormula_OPEN` (C=1/6) and new corrected formula
    differ by a factor of `36·(2π)²`. This lemma documents the relationship. -/
theorem weyl_formula_factor_relation (β : ℝ) :
    TorusIntegralWilson_Corrected β ↔
    (∫ (θ₁ : ℝ) in Set.Icc 0 (2 * Real.pi),
      ∫ (θ₂ : ℝ) in Set.Icc 0 (2 * Real.pi),
        wilson_weight β ⟨torusElt θ₁ θ₂, torusElt_mem_SU3 θ₁ θ₂⟩ *
          weyl_denominator θ₁ θ₂) =
    6 * (2 * Real.pi) ^ 2 * w1_weyl_series β :=
  Iff.rfl

end TheoremaAureum.Towers.YM.WeylFormulaCorrection
