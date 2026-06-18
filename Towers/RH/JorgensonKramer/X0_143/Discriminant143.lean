/-
  Towers/RH/JorgensonKramer/X0_143/Discriminant143.lean

  Defines ω = (1+α)/2 and states the discriminant certificate as named open surfaces.

  FULLY PROVED (0 sorry, classical trio):
    ω_sq_eq      : ω_val ^ 2 - ω_val + 36 = 0

  OPEN SURFACES (def Prop — not sorry, not axiom):
    Disc143_IntegralBasis_OPEN : ∃ b : Basis (Fin 2) ℤ (𝓞 K),
                                    Algebra.traceMatrix ℤ ↑b = !![ 2, 1; 1, -71 ]
      Proof sketch: ω_int = (1+α)/2 satisfies X²−X+36 (integral); {1,ω_int} spans 𝓞 K
      by the squarefree-143 discriminant argument; trace matrix follows from
      trace_localization (ℤ/ℚ/K tower).  Held OPEN pending trace_localization API
      alignment with Mathlib v4.12.0.

    K1_Discriminant_OPEN : NumberField.discr K = -143
      Follows from Disc143_IntegralBasis_OPEN via Algebra.discr_of_matrix_vecMul +
      norm_num det computation + discr_eq_discr.  Held OPEN together with the basis.

  SORRY: 0.  AXIOM FOOTPRINT: classical trio {propext, Classical.choice, Quot.sound}.
-/
import Mathlib.NumberTheory.NumberField.Discriminant
import Mathlib.RingTheory.Discriminant
import Towers.RH.JorgensonKramer.X0_143.Basic

namespace Towers.RH.JorgensonKramer.X0_143

open Polynomial NumberField Algebra

/-! ### ω = (1 + α) / 2 -/

/-- ω = (1+α)/2 in K = ℚ(√-143). -/
noncomputable def ω_val : K := (1 + α) / 2

/-- ω satisfies X² − X + 36 = 0:
    ω² − ω + 36 = ((1+α)² − 2(1+α) + 144) / 4 = (α² + 143) / 4 = 0. -/
lemma ω_sq_eq : ω_val ^ 2 - ω_val + 36 = 0 := by
  have h : ω_val ^ 2 - ω_val + (36 : K) = (α ^ 2 + 143) / 4 := by
    simp only [ω_val]; field_simp; ring
  rw [h, α_eval_zero, zero_div]

/-! ### Power basis and finrank -/

/-- Power basis for K/ℚ from the defining polynomial X^2 + C 143. -/
private noncomputable def pb_Kℚ : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis (show (X ^ 2 + C (143 : ℚ)) ≠ 0 from by norm_num)

/-- finrank ℚ K = 2. -/
theorem finrank_K_Q : FiniteDimensional.finrank ℚ K = 2 := by
  rw [pb_Kℚ.finrank]
  simp [pb_Kℚ, Polynomial.natDegree_X_pow_add_C]

/-! ### Named open surfaces -/

/-- OPEN: There exists a ℤ-basis b of 𝓞 K with trace matrix !![2,1;1,-71].
    Mathematical content: {1, ω_int} (ω_int = (1+α)/2) is a ℤ-basis; the trace
    values Tr(1)=2, Tr(ω)=1, Tr(ω²)=-71 follow from trace_localization over the
    ℤ/ℚ/K tower. -/
def Disc143_IntegralBasis_OPEN : Prop :=
  ∃ b : Basis (Fin 2) ℤ (𝓞 K),
    Algebra.traceMatrix ℤ (⇑b) = !![2, 1; 1, -71]

/-- OPEN: disc(K) = -143.
    Follows from Disc143_IntegralBasis_OPEN: obtain the ω-basis, compute
    det(!![2,1;1,-71]) = -143 by norm_num, conclude via discr_eq_discr. -/
def K1_Discriminant_OPEN : Prop := NumberField.discr K = -143

end Towers.RH.JorgensonKramer.X0_143
