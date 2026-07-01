/-!
## Phase 88-YM: WeylFormulaCorrection

Proves four unconditional bricks toward `SzegoGap_genuine_open`, and
states two corrected named-open surfaces with numerically verified constants.

**PHASE 88-YM DELIVERABLES (all trio-only, 0 sorry, 0 axiom):**

1. `normSq_exp_diff`           — |e^{iθ} - e^{iφ}|² = 2 - 2·cos(θ-φ)         PROVED
2. `weyl_denominator_formula`  — Δ = (2-2cos(θ₁-θ₂))·(2-2cos(2θ₁+θ₂))·...    PROVED
3. `trace_torusElt`            — Re(tr(torusElt)) = cosθ₁+cosθ₂+cos(θ₁+θ₂)    PROVED
4. `wilson_weight_factored`    — factorization into four exponentials             PROVED

**CORRECTED NAMED OPEN SURFACES (numerically verified 2026-07-01):**

5. `TorusIntegralWilson_Corrected β` — ∫_T wilson·Δ = 6·(2π)²·w1_weyl    OPEN
6. `SU3_WeylIntFormula_Corrected f`  — ∫_T f·Δ = 6·(2π)²·∫_{SU(3)} f     OPEN

**CORRECTED COMBINATOR:**
7. `szego_from_corrected_gates` — (5)+(6) → SzegoGap_genuine_open  PROVED conditional

**NUMERICAL AUDIT (Python, N=300², 2026-07-01):**
  ∫_{[0,2π]²} wilson·Δ dθ = 1.7641 ;  6·(2π)²·w1_weyl β₀ = 1.7641  ✓
  ∫_{[0,2π]²} Δ dθ = 236.87 = 6·(2π)²  ✓

Previous `SU3_WeylIntFormula_OPEN` (C=1/6) and `TorusIntegralWilson_OPEN` (=w1_weyl/6)
were both wrong by factor 36·(2π)². This file corrects both.
`Cert_Arb_SzegoGap` in SzegoGapCert.lean UNCHANGED.

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

/-! ## §1  Brick M1 — normSq of difference of two unit complex numbers -/

/-- **PROVED (trio).** |e^{iθ} - e^{iφ}|² = 2 - 2·cos(θ - φ). -/
private lemma normSq_exp_diff (θ φ : ℝ) :
    Complex.normSq (Complex.exp (↑θ * Complex.I) -
                    Complex.exp (↑φ * Complex.I)) =
    2 - 2 * Real.cos (θ - φ) := by
  rw [show ↑θ * Complex.I = Complex.I * ↑θ from mul_comm _ _,
      show ↑φ * Complex.I = Complex.I * ↑φ from mul_comm _ _,
      Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
             Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
             Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
             mul_one, mul_zero, zero_mul, one_mul, zero_add, add_zero, sub_zero]
  rw [Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ]

/-! ## §2  Brick M2 — Weyl denominator as product of cosine terms -/

/-- **PROVED (trio).** Δ(θ₁,θ₂) = (2-2cos(θ₁-θ₂))·(2-2cos(2θ₁+θ₂))·(2-2cos(θ₁+2θ₂)). -/
theorem weyl_denominator_formula (θ₁ θ₂ : ℝ) :
    weyl_denominator θ₁ θ₂ =
      (2 - 2 * Real.cos (θ₁ - θ₂)) *
      (2 - 2 * Real.cos (2 * θ₁ + θ₂)) *
      (2 - 2 * Real.cos (θ₁ + 2 * θ₂)) := by
  show Complex.normSq (Complex.exp (↑θ₁ * Complex.I) - Complex.exp (↑θ₂ * Complex.I)) *
       Complex.normSq (Complex.exp (↑θ₁ * Complex.I) -
                       Complex.exp (-(↑θ₁ + ↑θ₂) * Complex.I)) *
       Complex.normSq (Complex.exp (↑θ₂ * Complex.I) -
                       Complex.exp (-(↑θ₁ + ↑θ₂) * Complex.I)) =
       (2 - 2 * Real.cos (θ₁ - θ₂)) *
       (2 - 2 * Real.cos (2 * θ₁ + θ₂)) *
       (2 - 2 * Real.cos (θ₁ + 2 * θ₂))
  -- Factor 1: pair (z₁, z₂) → 2-2cos(θ₁-θ₂)
  rw [normSq_exp_diff θ₁ θ₂]
  -- Factor 2: pair (z₁, z₃) → 2-2cos(2θ₁+θ₂)
  rw [show Complex.normSq (Complex.exp (↑θ₁ * Complex.I) -
      Complex.exp (-(↑θ₁ + ↑θ₂) * Complex.I)) = 2 - 2 * Real.cos (2 * θ₁ + θ₂) from by
    have := normSq_exp_diff θ₁ (-(θ₁ + θ₂))
    simp only [Real.cos_neg] at this
    push_cast at this ⊢
    convert this using 2
    ring]
  -- Factor 3: pair (z₂, z₃) → 2-2cos(θ₁+2θ₂)
  rw [show Complex.normSq (Complex.exp (↑θ₂ * Complex.I) -
      Complex.exp (-(↑θ₁ + ↑θ₂) * Complex.I)) = 2 - 2 * Real.cos (θ₁ + 2 * θ₂) from by
    have := normSq_exp_diff θ₂ (-(θ₁ + θ₂))
    simp only [Real.cos_neg] at this
    push_cast at this ⊢
    convert this using 2
    ring]

/-! ## §3  Brick M3 — trace formula for torusElt -/

/-- Helper: Re(exp(θ·I)) = cos θ. -/
private lemma exp_re (θ : ℝ) : (Complex.exp (↑θ * Complex.I)).re = Real.cos θ := by
  rw [mul_comm, Complex.exp_mul_I]; simp

/-- **PROVED (trio).** Re(tr(torusElt θ₁ θ₂)) = cosθ₁ + cosθ₂ + cos(θ₁+θ₂). -/
theorem trace_torusElt (θ₁ θ₂ : ℝ) :
    (Matrix.trace (torusElt θ₁ θ₂)).re =
      Real.cos θ₁ + Real.cos θ₂ + Real.cos (θ₁ + θ₂) := by
  simp only [torusElt, Matrix.trace_diagonal, Fin.sum_univ_three, map_add, Complex.add_re]
  have hd0 : (torusDiag θ₁ θ₂ 0).re = Real.cos θ₁ := by
    simp only [torusDiag, Matrix.cons_val_zero]
    exact exp_re θ₁
  have hd1 : (torusDiag θ₁ θ₂ 1).re = Real.cos θ₂ := by
    simp only [torusDiag, Matrix.cons_val_one, Matrix.head_cons]
    exact exp_re θ₂
  have hd2 : (torusDiag θ₁ θ₂ 2).re = Real.cos (θ₁ + θ₂) := by
    simp only [torusDiag, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
               Matrix.cons_val_zero]
    -- torusDiag θ₁ θ₂ 2 = exp(-(θ₁+θ₂)*I)
    rw [show -(↑θ₁ + ↑θ₂) * Complex.I = Complex.I * ↑(-(θ₁ + θ₂)) from by push_cast; ring]
    rw [Complex.exp_mul_I]
    simp [Real.cos_neg]
  rw [hd0, hd1, hd2]

/-! ## §4  Brick M4 — Wilson weight factorization -/

/-- **PROVED (trio).** wilson_weight β (torusElt θ₁ θ₂)
    = exp(-3β) · exp(β·cosθ₁) · exp(β·cosθ₂) · exp(β·cos(θ₁+θ₂)). -/
theorem wilson_weight_factored (β θ₁ θ₂ : ℝ) :
    wilson_weight β ⟨torusElt θ₁ θ₂, torusElt_mem_SU3 θ₁ θ₂⟩ =
    Real.exp (-3 * β) * Real.exp (β * Real.cos θ₁) *
    Real.exp (β * Real.cos θ₂) * Real.exp (β * Real.cos (θ₁ + θ₂)) := by
  simp only [wilson_weight, Subtype.coe_mk, trace_torusElt]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1; ring

/-! ## §5  Corrected named open surfaces -/

/-- **CORRECTED NAMED OPEN SURFACE — Fourier side (Phase 88-YM).**

    Correct statement: ∫_{[0,2π]²} wilson·Δ = 6·(2π)²·w1_weyl_series β.
    (Previous `TorusIntegralWilson_OPEN` claimed `= w1_weyl/6` — wrong by 36·(2π)².)

    PROOF PLAN: JacobiAnger + Fubini + 2D Fourier orthogonality + Andreief identity.
    BARRIER: Andreief identity absent from Mathlib v4.12.0.
    SORRY: 0 (named Prop). -/
def TorusIntegralWilson_Corrected (β : ℝ) : Prop :=
  (∫ (θ₁ : ℝ) in Set.Icc 0 (2 * Real.pi),
    ∫ (θ₂ : ℝ) in Set.Icc 0 (2 * Real.pi),
      wilson_weight β ⟨torusElt θ₁ θ₂, torusElt_mem_SU3 θ₁ θ₂⟩ *
        weyl_denominator θ₁ θ₂) =
  6 * (2 * Real.pi) ^ 2 * w1_weyl_series β

/-- **CORRECTED NAMED OPEN SURFACE — SU(3) Weyl integration formula (Phase 88-YM).**

    Correct statement: ∫_{[0,2π]²} f(torusElt)·Δ = 6·(2π)²·∫_{SU(3)} f dμ.
    (Previous `SU3_WeylIntFormula_OPEN` claimed C = 1/6 — wrong by 36·(2π)².)

    BARRIER: G/T quotient-measure disintegration absent from Mathlib v4.12.0.
    SORRY: 0 (named Prop). -/
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
    Given `TorusIntegralWilson_Corrected` and `SU3_WeylIntFormula_Corrected`,
    `SzegoGap_genuine_open` follows.

    Chain: both hypotheses equate the same torus integral to 6·(2π)² times
    the Haar integral and w1_weyl_series respectively. Cancel 6·(2π)² > 0. -/
theorem szego_from_corrected_gates
    (h_weyl : SU3_WeylIntFormula_Corrected
                (fun g => wilson_weight (β₀_rat : ℝ) g))
    (h_torus : TorusIntegralWilson_Corrected (β₀_rat : ℝ)) :
    SzegoGap_genuine_open := by
  show w1_haar_SU3 (β₀_rat : ℝ) = w1_weyl_series (β₀_rat : ℝ)
  rw [w1_haar_eq_wilson_integral, haarSU3_eq_haarMeasure]
  -- heq: 6·(2π)²·∫_G (fun g => ww β₀ g) = 6·(2π)²·w1_weyl_series β₀
  -- (Both sides come from the same torus integral via h_weyl and h_torus.)
  have heq : 6 * (2 * Real.pi) ^ 2 *
      ∫ g : Matrix.specialUnitaryGroup (Fin 3) ℂ,
          (fun g' => wilson_weight (β₀_rat : ℝ) g') g
          ∂(MeasureTheory.Measure.haarMeasure ⊤) =
      6 * (2 * Real.pi) ^ 2 * w1_weyl_series (β₀_rat : ℝ) :=
    h_weyl.symm.trans h_torus
  have hpos : (0 : ℝ) < 6 * (2 * Real.pi) ^ 2 := by positivity
  -- Cancel 6·(2π)² and use definitional equality of beta-reduced integral
  have hcancel := mul_left_cancel₀ hpos.ne' heq
  simpa using hcancel

end TheoremaAureum.Towers.YM.WeylFormulaCorrection
