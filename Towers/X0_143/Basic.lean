/-
  Towers/RH/JorgensonKramer/X0_143/Basic.lean
  K = ℚ(√-143) as AdjoinRoot(X^2 + 143 : ℚ[X]).

  Instance chain (Mathlib v4.12.0):
    Field K       — AdjoinRoot.instField [Fact (Irreducible f)]
                    (RingTheory/AdjoinRoot.lean:346)
    NumberField K — anonymous instance [Fact (Irreducible f)]
                    (NumberTheory/NumberField/Basic.lean:344)

  Names that do NOT exist (zero grep hits) — never use:
    AdjoinRoot.numberField _ / AdjoinRoot.charZero _
    IsIntegralClosure.adjoinRoot_of_mod_four_eq_one
    discr_eq_discr_basis   (real API: discr_eq_discr with a Basis argument)
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Towers.RH.JorgensonKramer.X0_143

open Polynomial Real

/-! ### Irreducibility -/

/-- X^2 + 143 is irreducible over ℚ.
    Proof: monic degree-2 polynomial; any monic divisor of degree 1 would supply
    a rational root r with r^2 + 143 = 0, but r^2 ≥ 0 and 143 > 0. Axiom-free.
    Sage: PolynomialRing(QQ,'x')(x^2+143).is_irreducible() → True. -/
theorem X_sq_add_143_irred : Irreducible (X ^ 2 + C (143 : ℚ)) := by
  have hmonic : (X ^ 2 + C (143 : ℚ)).Monic :=
    monic_X_pow_add (degree_C_le.trans_lt (by norm_cast; norm_num))
  have hne1 : X ^ 2 + C (143 : ℚ) ≠ 1 := by
    intro h
    have h2 := congr_arg (coeff · 2) h
    simp only [coeff_add, coeff_X_pow, coeff_C, coeff_one, if_true, if_false] at h2
    norm_num at h2
  rw [hmonic.irreducible_iff_lt_natDegree_lt hne1]
  intro q hqm hqdeg hqdvd
  -- natDegree (X^2 + C 143) = 2, so Ioc 0 (2/2) = Ioc 0 1 = {1}
  have hnd2 : (X ^ 2 + C (143 : ℚ)).natDegree = 2 := by compute_degree!
  have hq1 : q.natDegree = 1 := by
    simp only [hnd2, show (2 : ℕ) / 2 = 1 from rfl, Finset.mem_Ioc] at hqdeg
    omega
  -- q has degree 1, so it has a rational root r
  have hqdeg1 : q.degree = 1 := by
    rw [degree_eq_natDegree hqm.ne_zero, hq1]; norm_cast
  obtain ⟨r, hr⟩ := exists_root_of_degree_eq_one hqdeg1
  -- r is also a root of X^2 + 143 (by transitivity of divisibility)
  have hroot : IsRoot (X ^ 2 + C (143 : ℚ)) r :=
    dvd_iff_isRoot.mp (dvd_trans (dvd_iff_isRoot.mpr hr) hqdvd)
  -- r^2 + 143 = 0 has no solution in ℚ
  simp only [IsRoot, eval_add, eval_pow, eval_X, eval_C] at hroot
  linarith [sq_nonneg r]

private instance : Fact (Irreducible (X ^ 2 + C (143 : ℚ))) :=
  ⟨X_sq_add_143_irred⟩

/-! ### Field K = ℚ(√-143) -/

/-- K := AdjoinRoot(X^2 + 143 : ℚ[X]). -/
def K : Type _ := AdjoinRoot (X ^ 2 + C (143 : ℚ))

noncomputable instance K_field : Field K := AdjoinRoot.instField _
noncomputable instance K_numberField : NumberField K := inferInstance

/-! ### Generator α with α^2 = -143 -/

/-- α := AdjoinRoot.root (X^2 + 143). -/
noncomputable def α : K := AdjoinRoot.root _

/-- α^2 + 143 = 0 in K.
    Proof: aeval_eq (@[simp]) + mk_self (@[simp]) → simp [α] closes the have;
    map_add/map_pow/aeval_X/aeval_C/map_ofNat expand the LHS. -/
lemma α_eval_zero : α ^ 2 + (143 : K) = 0 := by
  have hmk : Polynomial.aeval α (X ^ 2 + C (143 : ℚ)) = α ^ 2 + (143 : K) := by
    simp only [map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_ofNat]
  have h0 : Polynomial.aeval α (X ^ 2 + C (143 : ℚ)) = 0 := by simp [α]
  exact hmk.symm.trans h0

/-- α^2 = -143. -/
lemma α_sq : α ^ 2 = -(143 : K) := by linear_combination α_eval_zero

/-! ### Landau constant κ -/

/-- κ = 10π/√143 ≈ 2.624.
    Formula: κ = 2πh/(w√|disc|), h = h(K) = 10, w = 2, disc(K) = -143. -/
noncomputable def κ : ℝ := 10 * π / Real.sqrt 143

lemma κ_pos : 0 < κ := by unfold κ; positivity

end Towers.RH.JorgensonKramer.X0_143
