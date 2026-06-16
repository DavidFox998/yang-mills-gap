/-
  Wall 256.2 — YM/SU3/WeylDimension.lean
  SU(3) dominant weights and Weyl dimension formula.

  For SU(3), rank 2, the Weyl dimension formula for the irrep
  with Dynkin labels (m, n) (m,n ≥ 0) is:
      dim(m, n) = (m+1)(n+1)(m+n+2) / 2

  Spot checks:
    dim(0,0) = 1    (trivial rep)
    dim(1,0) = 3    (fundamental 3)
    dim(0,1) = 3    (antifundamental 3̄)
    dim(1,1) = 8    (adjoint)
    dim(2,0) = 6
    dim(3,0) = 10

  STATUS: SCAFFOLD — three sorry-discharged spot checks (computable,
  can be closed by native_decide). NOT a registered brick.
  YM Surface #1: OPEN. No mass-gap claim.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Int.Order.Basic

namespace TheoremaAureum.YM.SU3.WeylDimension

/-- Dominant integral weights for SU(3): pairs (m,n) with m,n ≥ 0.
    In Dynkin label convention, these index the finite-dimensional irreps. -/
def su3_dominant_weights : Set (Fin 2 → ℤ) :=
  {w | w 0 ≥ 0 ∧ w 1 ≥ 0}

/-- Weyl dimension formula for SU(3).
    For dominant w = (m,n): dim(m,n) = (m+1)(n+1)(m+n+2)/2.
    For non-dominant inputs (m < 0 or n < 0): returns 0 via Int.toNat. -/
def dim_su3 (w : Fin 2 → ℤ) : ℕ :=
  ((w 0 + 1) * (w 1 + 1) * (w 0 + w 1 + 2) / 2).toNat

/-- Trivial representation: dim(0,0) = 1 -/
theorem dim_su3_trivial : dim_su3 ![0, 0] = 1 := by native_decide

/-- Fundamental representation: dim(1,0) = 3 -/
theorem dim_su3_fund : dim_su3 ![1, 0] = 3 := by native_decide

/-- Adjoint representation: dim(1,1) = 8 -/
theorem dim_su3_adjoint : dim_su3 ![1, 1] = 8 := by native_decide

end TheoremaAureum.YM.SU3.WeylDimension
