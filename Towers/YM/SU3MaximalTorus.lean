import Mathlib
import Towers.YM.SU3Instances

/-!
# SU(3) Maximal Torus and Weyl Denominator

## Avenue 2 prerequisites (unconditional, classical trio, 0 sorry)

This file proves two necessary bricks toward `WeylIntegration_SU3_OPEN`
(Avenue 2 of the SzegoGap chain):

**Brick M1** — `torusElt_mem_SU3`:
  The parameterized torus family
    `torusElt θ₁ θ₂ = diag(e^{iθ₁}, e^{iθ₂}, e^{-i(θ₁+θ₂)})`
  lies in `SU(3) = specialUnitaryGroup (Fin 3) ℂ`.

**Brick M2** — `weyl_denominator_nonneg`:
  The SU(3) Weyl denominator
    `Δ(θ₁,θ₂) = ‖e^{iθ₁}-e^{iθ₂}‖² · ‖e^{iθ₁}-e^{-i(θ₁+θ₂)}‖² · ‖e^{iθ₂}-e^{-i(θ₁+θ₂)}‖²`
  satisfies `Δ ≥ 0` (product of `normSq` values).

**Named open surface** — `SU3_WeylIntFormula_OPEN`:
  The Weyl integration formula `∫_{SU(3)} f dμ = (1/6)∫_T f·Δ dθ₁dθ₂`
  remains OPEN: Mathlib v4.12.0 lacks quotient-measure theory for G/T.

These bricks are NECESSARY but not SUFFICIENT for Avenue 2.

SORRY: 0. Axiom footprint: `{propext, Classical.choice, Quot.sound}`.
YM Surface #1: LOCKED OPEN. No Clay claim.
-/

set_option maxHeartbeats 800000

namespace TheoremaAureum.Towers.YM.SU3MaximalTorus

open Matrix Complex Real MeasureTheory

abbrev SU3 := Matrix.specialUnitaryGroup (Fin 3) ℂ

-- ---------------------------------------------------------------------------
-- §1  The torus family
-- ---------------------------------------------------------------------------

/-- The three diagonal entries of a torus element:
    `(e^{iθ₁}, e^{iθ₂}, e^{-i(θ₁+θ₂)})`. -/
noncomputable def torusDiag (θ₁ θ₂ : ℝ) : Fin 3 → ℂ :=
  ![Complex.exp (θ₁ * Complex.I),
    Complex.exp (θ₂ * Complex.I),
    Complex.exp (-(θ₁ + θ₂) * Complex.I)]

/-- The torus element: diagonal SU(3) matrix with eigenvalues on the unit circle. -/
noncomputable def torusElt (θ₁ θ₂ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  diagonal (torusDiag θ₁ θ₂)

-- ---------------------------------------------------------------------------
-- §2  Key helper: star(exp(θ·I)) = exp(-θ·I)  and  star·self = 1
-- ---------------------------------------------------------------------------

/-- Complex conjugation reverses the sign: `star(exp(↑θ·I)) = exp(-↑θ·I)`. -/
private lemma star_exp_ofReal_mul_I (θ : ℝ) :
    star (Complex.exp (↑θ * Complex.I)) = Complex.exp (-(↑θ) * Complex.I) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I, neg_mul]

/-- `exp(-↑θ·I) * exp(↑θ·I) = 1` via `exp_add` + `exp_zero`. -/
private lemma exp_neg_mul_exp_ofReal_mul_I (θ : ℝ) :
    Complex.exp (-(↑θ) * Complex.I) * Complex.exp (↑θ * Complex.I) = 1 := by
  rw [← Complex.exp_add]
  norm_num [Complex.exp_zero]

/-- `star(exp(↑θ·I)) * exp(↑θ·I) = 1`. -/
private lemma star_mul_self_exp_ofReal_mul_I (θ : ℝ) :
    star (Complex.exp (↑θ * Complex.I)) * Complex.exp (↑θ * Complex.I) = 1 := by
  rw [star_exp_ofReal_mul_I]
  exact exp_neg_mul_exp_ofReal_mul_I θ

-- ---------------------------------------------------------------------------
-- §3  Brick M1 — torusElt lies in SU(3)
-- ---------------------------------------------------------------------------

/-- **Brick M1** — `torusElt_mem_SU3`:
    Every element of the parameterized torus lies in `SU(3)`.

    * **Unitarity:** `(diagonal d)ᴴ * diagonal d = diagonal (star d · d) = 1`
      because `star(exp(θ·I)) · exp(θ·I) = exp(-θ·I) · exp(θ·I) = 1`.
    * **det = 1:** `det(diagonal d) = d₀·d₁·d₂ = exp(i(θ₁+θ₂-θ₁-θ₂)) = exp(0) = 1`.

    SORRY: 0. Classical trio only. -/
theorem torusElt_mem_SU3 (θ₁ θ₂ : ℝ) : torusElt θ₁ θ₂ ∈ SU3 := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · -- Unitarity: (torusElt θ₁ θ₂) ∈ unitaryGroup
    rw [Matrix.mem_unitaryGroup_iff, torusElt,
        Matrix.conjTranspose_diagonal, Matrix.diagonal_mul_diagonal]
    rw [show (fun i => star (torusDiag θ₁ θ₂ i) * torusDiag θ₁ θ₂ i) = (fun _ => 1) from by
      funext i
      fin_cases i
      · -- i = 0
        simp only [torusDiag, Matrix.cons_val_zero]
        exact star_mul_self_exp_ofReal_mul_I θ₁
      · -- i = 1
        simp only [torusDiag, Matrix.cons_val_one, Matrix.head_cons]
        exact star_mul_self_exp_ofReal_mul_I θ₂
      · -- i = 2
        simp only [torusDiag, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        exact star_mul_self_exp_ofReal_mul_I (-(θ₁ + θ₂))]
    exact Matrix.diagonal_one
  · -- det = 1
    simp only [torusElt, Matrix.det_diagonal, torusDiag]
    rw [Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Matrix.cons_val_two, Matrix.tail_cons]
    rw [← Complex.exp_add, ← Complex.exp_add]
    norm_num [Complex.exp_zero]

-- ---------------------------------------------------------------------------
-- §4  The torus is abelian and closed under parameter addition
-- ---------------------------------------------------------------------------

/-- Torus elements commute (T is abelian). -/
theorem torusElt_comm (θ₁ θ₂ θ₃ θ₄ : ℝ) :
    torusElt θ₁ θ₂ * torusElt θ₃ θ₄ = torusElt θ₃ θ₄ * torusElt θ₁ θ₂ := by
  simp only [torusElt, torusDiag, Matrix.diagonal_mul_diagonal]
  congr 1; funext i; fin_cases i <;> simp [mul_comm]

/-- The torus is closed under parameter addition:
    `torusElt (θ₁+θ₃) (θ₂+θ₄) = torusElt θ₁ θ₂ * torusElt θ₃ θ₄`. -/
theorem torusElt_mul (θ₁ θ₂ θ₃ θ₄ : ℝ) :
    torusElt θ₁ θ₂ * torusElt θ₃ θ₄ = torusElt (θ₁ + θ₃) (θ₂ + θ₄) := by
  simp only [torusElt, torusDiag, Matrix.diagonal_mul_diagonal]
  congr 1; funext i
  fin_cases i
  · simp only [Matrix.cons_val_zero, ← Complex.exp_add, push_cast]
    ring_nf
  · simp only [Matrix.cons_val_one, Matrix.head_cons, ← Complex.exp_add, push_cast]
    ring_nf
  · simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
               ← Complex.exp_add, push_cast]
    congr 1; push_cast; ring

/-- The identity `torusElt 0 0 = 1` (torus contains the identity). -/
theorem torusElt_zero : torusElt 0 0 = 1 := by
  simp only [torusElt, torusDiag]
  norm_num [Matrix.diagonal_one, Matrix.one_fin_three]

-- ---------------------------------------------------------------------------
-- §5  Brick M2 — Weyl denominator
-- ---------------------------------------------------------------------------

/-- **Brick M2** — the SU(3) Weyl denominator.

    For eigenvalues `e^{iθ₁}, e^{iθ₂}, e^{-i(θ₁+θ₂)}` of `torusElt θ₁ θ₂`,
    the Weyl denominator is the product over the three positive roots:

      `Δ(θ₁,θ₂) = |e^{iθ₁}-e^{iθ₂}|² · |e^{iθ₁}-e^{-i(θ₁+θ₂)}|² · |e^{iθ₂}-e^{-i(θ₁+θ₂)}|²`

    This is the integrating kernel in the Weyl integration formula for SU(3).
    The formula itself is the content of `SU3_WeylIntFormula_OPEN` below. -/
noncomputable def weyl_denominator (θ₁ θ₂ : ℝ) : ℝ :=
  let z₁ := Complex.exp (θ₁ * Complex.I)
  let z₂ := Complex.exp (θ₂ * Complex.I)
  let z₃ := Complex.exp (-(θ₁ + θ₂) * Complex.I)
  Complex.normSq (z₁ - z₂) * Complex.normSq (z₁ - z₃) * Complex.normSq (z₂ - z₃)

/-- **Brick M2a** — the Weyl denominator is nonneg (product of `normSq` values). -/
theorem weyl_denominator_nonneg (θ₁ θ₂ : ℝ) : 0 ≤ weyl_denominator θ₁ θ₂ :=
  mul_nonneg (mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
    (Complex.normSq_nonneg _)

/-- **Brick M2b** — Δ(θ₁,θ₂) = Δ(θ₂,θ₁) (symmetry under permutation of eigenvalues). -/
theorem weyl_denominator_symm (θ₁ θ₂ : ℝ) :
    weyl_denominator θ₁ θ₂ = weyl_denominator θ₂ θ₁ := by
  simp only [weyl_denominator, add_comm θ₁ θ₂]
  ring

-- ---------------------------------------------------------------------------
-- §6  Named open surface — Avenue 2 gate
-- ---------------------------------------------------------------------------

/-- **NAMED OPEN SURFACE — Avenue 2: SU(3) Weyl Integration Formula.**

    The Weyl integration formula reduces the `SU(3)` Haar integral to a
    two-dimensional torus integral:

      `∫_{SU(3)} f dμ = (1/|W|) · ∫_{[0,2π]²} f(torusElt θ₁ θ₂) · Δ(θ₁,θ₂) dθ₁ dθ₂`

    where `Δ = weyl_denominator` and `|W| = 6` (size of the Weyl group S₃).

    **Barrier (as of Mathlib v4.12.0):**
    (a) Quotient-measure theory for G/T: `G/T` as a measurable space and the
        disintegration `μ_G = ∫_T μ_{G/T} dμ_T` — NOT in Mathlib.
    (b) Abstract Weyl integration theorem for compact Lie groups — NOT in Mathlib.

    `torusElt_mem_SU3` and `weyl_denominator_nonneg` are NECESSARY prerequisites
    proved in this file. The full formula requires the missing (a)+(b).

    Estimated effort: 6–12 months (new Mathlib module needed).
    SORRY: 0 (open Prop, not sorry). YM Surface #1: LOCKED OPEN. -/
def SU3_WeylIntFormula_OPEN
    (f : Matrix.specialUnitaryGroup (Fin 3) ℂ → ℝ) : Prop :=
  ∃ (C : ℝ), C = 1 / 6 ∧
  (∫ (θ₁ : ℝ) in Set.Icc 0 (2 * Real.pi),
     ∫ (θ₂ : ℝ) in Set.Icc 0 (2 * Real.pi),
       f ⟨torusElt θ₁ θ₂, torusElt_mem_SU3 θ₁ θ₂⟩ * weyl_denominator θ₁ θ₂) =
  C * (∫ (g : Matrix.specialUnitaryGroup (Fin 3) ℂ),
         f g ∂(MeasureTheory.Measure.haarMeasure ⊤))

end TheoremaAureum.Towers.YM.SU3MaximalTorus
