/-
SzegoFromWeyl.lean — Reduces SzegoGap_genuine_open to two precise named sub-gates:

  (A) SU3_WeylIntFormula_OPEN (fun g => wilson_weight β₀ g)
        — SU(3) Weyl integration formula for the Wilson weight  [6-12 months]
  (B) TorusIntegralWilson_OPEN β₀
        — Torus integral of the Wilson weight = w1_weyl_series β₀ / 6  [2-4 weeks]

szego_from_weyl_and_torus proves SzegoGap_genuine_open from (A) + (B) with 0 sorry.

Chain:
  (A) integral_T f*Delta d(theta1)d(theta2) = (1/6) * integral_G f d(mu_G)  [Weyl]
  (B) integral_T f*Delta d(theta1)d(theta2) = w1_weyl_series beta0 / 6      [JA + Fourier]
  =>  (1/6) * integral_G = w1_weyl_series beta0 / 6
  =>  integral_G = w1_weyl_series beta0
  =>  w1_haar_SU3 beta0 = w1_weyl_series beta0   [def of w1_haar_SU3]
  =>  SzegoGap_genuine_open                        [def of SzegoGap]

SORRY: 0. Axioms: {propext, Classical.choice, Quot.sound}.
YM Surface #1: LOCKED OPEN. No Clay claim.
-/

import Towers.YM.SU3MaximalTorus
import Towers.YM.YMMasterCombinator

set_option maxHeartbeats 400000

namespace TheoremaAureum.Towers.YM.SzegoFromWeyl

open Real Matrix MeasureTheory
open TheoremaAureum.Towers.YM.SU3MaximalTorus
open TheoremaAureum.Towers.YM.WeylToeplitzBound
open TheoremaAureum.Towers.YM.MasterCombinator
open TheoremaAureum.Towers.YM.SU3Instances

/-! ## §1  The Wilson weight function -/

/-- The single-site Gross-Witten weight function on SU(3).
    `wilson_weight beta g = exp(-beta * (3 - Re(tr g)))`. -/
noncomputable def wilson_weight
    (beta : Real) (g : Matrix.specialUnitaryGroup (Fin 3) Complex) : Real :=
  Real.exp (-beta * (3 - (Matrix.trace (g.val : Matrix (Fin 3) (Fin 3) Complex)).re))

/-- `w1_haar_SU3 beta` is the integral of `wilson_weight beta` against `haarSU3`.
    Definitional: both sides unfold to `MeasureTheory.integral haarSU3 (...)`. -/
lemma w1_haar_eq_wilson_integral (beta : Real) :
    w1_haar_SU3 beta =
      integral (haarSU3 : Measure (Matrix.specialUnitaryGroup (Fin 3) Complex))
        (fun g => wilson_weight beta g) := rfl

/-- Definitional equality: `haarSU3 = haarMeasure top` (from SU3Instances). -/
lemma haarSU3_eq_haarMeasure :
    (haarSU3 : Measure (Matrix.specialUnitaryGroup (Fin 3) Complex)) =
      MeasureTheory.Measure.haarMeasure ⊤ := rfl

/-! ## §2  Named open surface: torus integral of the Gross-Witten weight -/

/-- **NAMED OPEN SURFACE (2026-06-28) — SU(3) torus integral of the Wilson weight.**

    `TorusIntegralWilson_OPEN beta` states that the two-dimensional integral over the
    maximal torus parameterized by `torusElt theta1 theta2` satisfies:

      integral_{[0,2pi]^2} wilson_weight beta (torusElt theta1 theta2) * Delta dtheta1 dtheta2
        = w1_weyl_series beta / 6

    where `Delta = weyl_denominator` is the SU(3) Weyl denominator
    `|e^{i*theta1} - e^{i*theta2}|^2 * |e^{i*theta1} - e^{-i(theta1+theta2)}|^2 * ...`.

    **Normalization:** The `/ 6 = / |W|` factor (Weyl group S_3) cancels with
    `C = 1/6` in `SU3_WeylIntFormula_OPEN`, yielding `w1_haar_SU3 beta = w1_weyl_series beta`.

    **Proof sketch using JacobiAnger_FormCoeff (PROVED in JacobiAngerAvenue1):**
    Step 1. Factor: exp(-beta*(3-Re tr)) = exp(-beta)*exp(beta*cos theta1)*...*exp(beta*cos(theta1+theta2))
    Step 2. Jacobi-Anger (proved): exp(beta*cos theta) = sum_{n in Z} I_n(beta) * exp(i*n*theta)
    Step 3. Expand Delta as trigonometric polynomial on T^2
    Step 4. Integrate: 2D Fourier orthogonality on T^2 selects surviving modes
    Step 5. Sum assembles into exp(-beta) * sum_k det[I_{|i-j-k|}(beta/3)]_{0<=i,j<=2}
             = w1_weyl_series beta

    **Barriers (Mathlib v4.12.0 gaps):**
    (a) `integral_tsum` for 2-variable Fourier products on T^2 (1D exists; 2D missing)
    (b) 2D Fourier orthogonality: integral e^{i(m1-n1)theta1} * e^{i(m2-n2)theta2} = (2pi)^2 * delta*delta
    (c) Weyl denominator Fourier expansion as trigonometric polynomial on T^2
    Steps 1-2 use the proved JacobiAnger_FormCoeff; steps 3-5 need (a)-(c).
    Estimated effort: 2-4 weeks (shorter than Avenue 2).

    SORRY: 0 (named Prop, not sorry).  YM Surface #1: LOCKED OPEN. -/
def TorusIntegralWilson_OPEN (beta : Real) : Prop :=
  (∫ (theta1 : Real) in Set.Icc 0 (2 * Real.pi),
     ∫ (theta2 : Real) in Set.Icc 0 (2 * Real.pi),
       wilson_weight beta ⟨torusElt theta1 theta2, torusElt_mem_SU3 theta1 theta2⟩ *
         weyl_denominator theta1 theta2) =
  w1_weyl_series beta / 6

/-! ## §3  Wiring theorem: Weyl formula + torus integral -> SzegoGap_genuine_open -/

/-- **CONDITIONAL (classical trio, 0 sorry) — precise wiring of SzegoGap_genuine_open.**

    Given:
    * `h_weyl` : SU3_WeylIntFormula_OPEN for f = wilson_weight beta0
      States: exists C = 1/6, integral_T f*Delta = C * integral_G f d(mu_G)
    * `h_torus` : TorusIntegralWilson_OPEN at beta = beta0
      States: integral_T wilson_weight beta0 * Delta = w1_weyl_series beta0 / 6

    Conclude: SzegoGap_genuine_open (= w1_haar_SU3 beta0 = w1_weyl_series beta0).

    **6-step arithmetic chain (classical trio, 0 sorry):**
    (1) h_weyl gives: integral_T = C * integral_G
    (2) h_torus gives: integral_T = w1_weyl_series beta0 / 6
    (3) Combine: C * integral_G = w1_weyl_series beta0 / 6
    (4) Use hC (C = 1/6): (1/6) * integral_G = w1_weyl_series beta0 / 6
    (5) Multiply by 6 (linear_combination): integral_G = w1_weyl_series beta0
    (6) integral_G wilson_weight beta0 = w1_haar_SU3 beta0 (def of w1_haar_SU3)

    Once SU3_WeylIntFormula_OPEN and TorusIntegralWilson_OPEN are formalized,
    SzegoGap_genuine_open closes immediately from this theorem. -/
theorem szego_from_weyl_and_torus
    (h_weyl : SU3_WeylIntFormula_OPEN
                (fun g : Matrix.specialUnitaryGroup (Fin 3) Complex =>
                  wilson_weight (β₀_rat : Real) g))
    (h_torus : TorusIntegralWilson_OPEN (β₀_rat : Real)) :
    SzegoGap_genuine_open := by
  show w1_haar_SU3 (β₀_rat : Real) = w1_weyl_series (β₀_rat : Real)
  rw [w1_haar_eq_wilson_integral, haarSU3_eq_haarMeasure]
  obtain ⟨C, hC, hWeyl⟩ := h_weyl
  -- Coerce h_torus to lambda form matching hWeyl's LHS
  -- (definitional: wilson_weight beta g = (fun g' => wilson_weight beta g') g)
  have htdef : ∫ (theta1 : Real) in Set.Icc 0 (2 * Real.pi),
      ∫ (theta2 : Real) in Set.Icc 0 (2 * Real.pi),
        (fun g : Matrix.specialUnitaryGroup (Fin 3) Complex =>
            wilson_weight (β₀_rat : Real) g)
          ⟨torusElt theta1 theta2, torusElt_mem_SU3 theta1 theta2⟩ *
          weyl_denominator theta1 theta2 =
      w1_weyl_series (β₀_rat : Real) / 6 := h_torus
  -- Chain: C * integral_G = integral_T = w1_weyl_series beta0 / 6
  have eq1 : C * integral (MeasureTheory.Measure.haarMeasure ⊤)
                   (fun g : Matrix.specialUnitaryGroup (Fin 3) Complex =>
                     (fun g' => wilson_weight (β₀_rat : Real) g') g) =
               w1_weyl_series (β₀_rat : Real) / 6 :=
    hWeyl.symm.trans htdef
  -- Specialize C = 1/6
  have eq2 : (1 / 6 : Real) * integral (MeasureTheory.Measure.haarMeasure ⊤)
                   (fun g : Matrix.specialUnitaryGroup (Fin 3) Complex =>
                     (fun g' => wilson_weight (β₀_rat : Real) g') g) =
               w1_weyl_series (β₀_rat : Real) / 6 := by rw [← hC]; exact eq1
  -- Beta-reduce the lambda, then (1/6)*x = y/6 -> x = y
  simp only [] at eq2
  linear_combination 6 * eq2

/-! ## §4  Summary combinator -/

/-- **CONDITIONAL (classical trio, 0 sorry) — implication summary.**

    SzegoGap_genuine_open <- SU3_WeylIntFormula_OPEN f_wilson /\ TorusIntegralWilson_OPEN beta0

    The two sub-gates are INDEPENDENT:
    * TorusIntegralWilson_OPEN: purely analytic (T^2 Fourier on R), no Lie theory needed.
      Proof plan uses only the proved JacobiAnger_FormCoeff + 2D Fourier orthogonality.
    * SU3_WeylIntFormula_OPEN: purely measure-theoretic (G -> G/T disintegration).
      Does not require JacobiAnger. Independent Mathlib module needed.

    Either sub-gate can be formalized independently. -/
theorem szego_genuine_decomp :
    (SU3_WeylIntFormula_OPEN
        (fun g : Matrix.specialUnitaryGroup (Fin 3) Complex =>
          wilson_weight (β₀_rat : Real) g) ∧
      TorusIntegralWilson_OPEN (β₀_rat : Real)) →
    SzegoGap_genuine_open :=
  fun ⟨hw, ht⟩ => szego_from_weyl_and_torus hw ht

end TheoremaAureum.Towers.YM.SzegoFromWeyl
