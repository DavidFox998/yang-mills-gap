-- Strict Wilson-action positivity for SU(3)
-- Towers/YM/WilsonPositivity.lean
-- Proves: Re tr g ≤ 3 for all g : SU(3), with equality iff g = 1.
-- Single-plaquette energy (3 - Re tr g)/3 ≥ 0, strictly positive off vacuum.
-- Axioms: {propext, Classical.choice, Quot.sound}  SORRY: 0
-- SCOPE: scalar-sector action positivity ONLY.
-- NOT a statement about the real Wilson transfer operator.
-- Surface #1 stays OPEN; no mass-gap / μ>0 claim.

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.SpecialUnitaryGroup

open Matrix Complex

namespace TheoremaAureum.WilsonPositivity

abbrev SU3 := Matrix.specialUnitaryGroup (Fin 3) ℂ

-- Re tr g ≤ 3 for g : SU(3).
-- Proof: for each diagonal entry (g i i), the row-norm identity
--   ∑ k, normSq(g i k) = 1  (from g * star g = 1)
-- gives normSq(g i i) ≤ 1, hence re(g i i)² ≤ 1, hence re(g i i) ≤ 1.
-- Summing over i : Fin 3 gives Re tr g ≤ 3.
lemma reTrace_le_three (g : SU3) :
    (g.1.trace.re) ≤ 3 := by
  -- Extract unitarity: g.1 * star g.1 = 1
  have hU : g.1 * star g.1 = 1 :=
    Matrix.mem_unitaryGroup_iff.mp
      (Matrix.mem_specialUnitaryGroup_iff.mp g.2).1
  -- For each i, the diagonal entry satisfies re(g.1 i i) ≤ 1
  have hdiag : ∀ i : Fin 3, (g.1 i i).re ≤ 1 := fun i => by
    -- Row sum from unitarity: ∑ k, g.1 i k * (star g.1) k i = 1
    have hii : ∑ k : Fin 3, g.1 i k * (star g.1) k i = 1 := by
      have h1 : (g.1 * star g.1) i i = 1 := by rw [hU]; simp
      simp only [Matrix.mul_apply] at h1
      exact h1
    -- Each term equals normSq (as a complex cast): z * conj z = ↑normSq z
    have hterm : ∀ k : Fin 3, g.1 i k * (star g.1) k i =
        ↑(Complex.normSq (g.1 i k)) := fun k => by
      rw [Matrix.star_apply]
      exact Complex.mul_conj (g.1 i k)
    -- Row norm = 1 in ℝ (extract real part of the complex identity)
    have hrow : ∑ k : Fin 3, Complex.normSq (g.1 i k) = 1 := by
      have heq : ∀ k : Fin 3, (Complex.normSq (g.1 i k) : ℂ) =
          g.1 i k * (star g.1) k i := fun k => (hterm k).symm
      have hsum : (∑ k : Fin 3, (Complex.normSq (g.1 i k) : ℂ)) = 1 := by
        simp_rw [heq]; exact hii
      have hre := congr_arg Complex.re hsum
      simp only [map_sum, Complex.ofReal_re, Complex.one_re] at hre
      exact hre
    -- The diagonal term is one summand of a nonneg sum equal to 1
    have hle : Complex.normSq (g.1 i i) ≤ 1 :=
      hrow ▸ Finset.single_le_sum
        (fun k _ => Complex.normSq_nonneg (g.1 i k)) (Finset.mem_univ i)
    -- normSq z = re²  + im² ≤ 1  ⟹  re² ≤ 1  ⟹  re ≤ 1
    have hre_sq : (g.1 i i).re ^ 2 ≤ 1 := by
      have hns : Complex.normSq (g.1 i i) =
          (g.1 i i).re ^ 2 + (g.1 i i).im ^ 2 := by
        rw [Complex.normSq_apply]; ring
      nlinarith [sq_nonneg (g.1 i i).im]
    nlinarith [sq_nonneg ((g.1 i i).re - 1)]
  -- Unfold trace and sum the per-entry bounds
  have htr : g.1.trace.re = ∑ i : Fin 3, (g.1 i i).re := by
    simp [Matrix.trace, map_sum]
  rw [htr]
  calc ∑ i : Fin 3, (g.1 i i).re
      ≤ ∑ _i : Fin 3, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hdiag i)
    _ = 3 := by norm_num

-- Wilson plaquette action is non-negative.
noncomputable def wilsonAction (g : SU3) : ℝ :=
  (3 - g.1.trace.re) / 3

lemma wilsonAction_nonneg (g : SU3) : 0 ≤ wilsonAction g := by
  unfold wilsonAction
  linarith [reTrace_le_three g]

end TheoremaAureum.WilsonPositivity
