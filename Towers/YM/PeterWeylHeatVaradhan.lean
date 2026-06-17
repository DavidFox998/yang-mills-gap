-- Towers/YM/PeterWeylHeatVaradhan.lean
-- SU(3) heat-kernel envelope — strip-form Varadhan bound infrastructure
-- David Fox | Theorema Aureum 143 | 2026-06-14
--
-- HONESTY HEADER
-- Status: proved.  Zero sorry.  Zero native_decide.  Zero axiom.
-- Axiom footprint: {propext, Classical.choice, Quot.sound}
--
-- Three namespaces (opened by VaradhanStripWidened.lean):
--   TheoremaAureum.Towers.YM.PeterWeylHeat       — envelope def + monotonicity
--   TheoremaAureum.Towers.YM.PeterWeylHeatVaradhan — strip constants + bound
--   TheoremaAureum.Towers.YM.RiemannianGeometry    — d_SU3 placeholder + SU3 alias
--
-- HONEST CAVEAT (carried from Task #156):
--   Heat_kernel_envelope_real is defined here as exp(1/t) — a concrete
--   stand-in that is antitone and ≥ 1 for t > 0.  The genuine SU(3)
--   on-diagonal heat trace blows up like C/t^4 as t→0⁺, NOT as exp(1/t).
--   The strip bound is valid on the chosen closed window [t_lo, t_top] with
--   0 < t_lo.  The Varadhan shape exp(-c/t) / t^4 is mathematically FALSE
--   on any neighbourhood of 0.  YM Surface #1 stays OPEN.
--
-- d_SU3 is a zero-constant placeholder for the genuine SU(3) Killing-form
-- chordal distance; the geometric bound theorems in VaradhanStripWidened are
-- conditioned on d_SU3 x 1 = 0 (diagonal hypothesis) and are therefore
-- non-vacuous only modulo the real metric definition.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Towers.YM.SU3Instances

-- ===========================================================================
-- Namespace 1: PeterWeylHeat
-- Abstract heat-kernel envelope and its key properties (antitone, ≥ 1).
-- ===========================================================================

namespace TheoremaAureum.Towers.YM.PeterWeylHeat

open Real

/-- Stand-in heat-kernel envelope: exp(1/t).
    Honest caveat: the genuine SU(3) on-diagonal trace is ≍ C/t⁴ near t=0⁺,
    NOT exp(1/t).  This function is used only as a concrete antitone stand-in
    that satisfies ge_one_of_pos on (0,∞) and is compatible with the strip
    bound algebra.  YM Surface #1 stays OPEN. -/
noncomputable def Heat_kernel_envelope_real (t : ℝ) : ℝ := Real.exp (1 / t)

/-- The envelope is ≥ 1 for every t > 0. -/
theorem Heat_kernel_envelope_real_ge_one_of_pos {t : ℝ} (ht : 0 < t) :
    1 ≤ Heat_kernel_envelope_real t := by
  unfold Heat_kernel_envelope_real
  calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp (1 / t) :=
          Real.exp_le_exp.mpr (div_nonneg one_pos.le ht.le)

/-- The envelope is antitone on (0,∞): 0 < a ≤ b → env(b) ≤ env(a). -/
theorem Heat_kernel_envelope_real_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Heat_kernel_envelope_real b ≤ Heat_kernel_envelope_real a := by
  unfold Heat_kernel_envelope_real
  apply Real.exp_le_exp.mpr
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [div_le_div_iff hb ha]
  linarith

end TheoremaAureum.Towers.YM.PeterWeylHeat

-- ===========================================================================
-- Namespace 2: PeterWeylHeatVaradhan
-- Strip endpoints, decay constant, amplitude, and the original strip bound.
-- ===========================================================================

namespace TheoremaAureum.Towers.YM.PeterWeylHeatVaradhan

open Real TheoremaAureum.Towers.YM.PeterWeylHeat

/-- Strip lower endpoint: t_lo = 1/100. -/
noncomputable def varadhan_t_lo : ℝ := 1 / 100

/-- Strip upper endpoint: t_top = 100. -/
noncomputable def varadhan_t_top : ℝ := 100

/-- Exponential decay constant: c = 1. -/
noncomputable def varadhan_c : ℝ := 1

theorem varadhan_t_lo_pos : 0 < varadhan_t_lo := by
  unfold varadhan_t_lo; norm_num

theorem varadhan_t_top_pos : 0 < varadhan_t_top := by
  unfold varadhan_t_top; norm_num

theorem varadhan_c_pos : 0 < varadhan_c := by
  unfold varadhan_c; norm_num

/-- Original strip amplitude, chosen so that the strip bound holds on
    [varadhan_t_lo, varadhan_t_top]. -/
noncomputable def varadhan_C : ℝ :=
  Heat_kernel_envelope_real varadhan_t_lo *
    varadhan_t_top ^ 4 *
      Real.exp (varadhan_c / varadhan_t_lo)

theorem varadhan_C_pos : 0 < varadhan_C := by
  unfold varadhan_C
  have henv : 1 ≤ Heat_kernel_envelope_real varadhan_t_lo :=
    Heat_kernel_envelope_real_ge_one_of_pos varadhan_t_lo_pos
  have htop4 : (0 : ℝ) < varadhan_t_top ^ 4 := pow_pos varadhan_t_top_pos 4
  have hexp : (0 : ℝ) < Real.exp (varadhan_c / varadhan_t_lo) := Real.exp_pos _
  exact mul_pos (mul_pos (by linarith) htop4) hexp

/-- **Strip-form Varadhan-shape upper bound (original strip).**
    For t ∈ [varadhan_t_lo, varadhan_t_top]:
      Heat_kernel_envelope_real t ≤ varadhan_C · exp(-c/t) / t⁴.
    Proof: antitonicity bounds env(t) ≤ env(t_lo); the algebra factors out
    t_top⁴ and exp(c/t_lo)·exp(-c/t) ≥ 1, giving the bound. -/
theorem Heat_kernel_envelope_real_le_varadhan
    {t : ℝ} (ht_lo : varadhan_t_lo ≤ t) (ht_top : t ≤ varadhan_t_top) :
    Heat_kernel_envelope_real t ≤
      varadhan_C * Real.exp (-(varadhan_c / t)) / t ^ 4 := by
  have htpos : 0 < t := lt_of_lt_of_le varadhan_t_lo_pos ht_lo
  have ht4_pos : 0 < t ^ 4 := pow_pos htpos 4
  have hmono : Heat_kernel_envelope_real t ≤ Heat_kernel_envelope_real varadhan_t_lo :=
    Heat_kernel_envelope_real_antitone varadhan_t_lo_pos ht_lo
  have hep_nonneg : 0 ≤ Heat_kernel_envelope_real varadhan_t_lo := by
    linarith [Heat_kernel_envelope_real_ge_one_of_pos varadhan_t_lo_pos]
  have htop4_pos : 0 < varadhan_t_top ^ 4 := pow_pos varadhan_t_top_pos 4
  -- (a) c/t ≤ c/t_lo since 0 < t_lo ≤ t and c > 0.
  have hclo : varadhan_c / t ≤ varadhan_c / varadhan_t_lo := by
    rw [div_le_div_iff htpos varadhan_t_lo_pos]
    have := mul_le_mul_of_nonneg_left ht_lo varadhan_c_pos.le
    linarith
  -- (b) exp(c/t_lo) · exp(-c/t) ≥ 1.
  have hexp_ineq :
      1 ≤ Real.exp (varadhan_c / varadhan_t_lo) * Real.exp (-(varadhan_c / t)) := by
    rw [← Real.exp_add]
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (varadhan_c / varadhan_t_lo + -(varadhan_c / t)) :=
            Real.exp_le_exp.mpr (by linarith)
  -- (c) t⁴ ≤ t_top⁴.
  have ht4_le : t ^ 4 ≤ varadhan_t_top ^ 4 :=
    pow_le_pow_left htpos.le ht_top 4
  -- Combine.
  have hrhs :
      Heat_kernel_envelope_real varadhan_t_lo ≤
        varadhan_C * Real.exp (-(varadhan_c / t)) / t ^ 4 := by
    rw [le_div_iff₀ ht4_pos]
    have hC_eq :
        varadhan_C * Real.exp (-(varadhan_c / t)) =
          Heat_kernel_envelope_real varadhan_t_lo *
            varadhan_t_top ^ 4 *
              (Real.exp (varadhan_c / varadhan_t_lo) *
                Real.exp (-(varadhan_c / t))) := by
      unfold varadhan_C; ring
    rw [hC_eq]
    calc Heat_kernel_envelope_real varadhan_t_lo * t ^ 4
        ≤ Heat_kernel_envelope_real varadhan_t_lo * varadhan_t_top ^ 4 :=
            mul_le_mul_of_nonneg_left ht4_le hep_nonneg
      _ = Heat_kernel_envelope_real varadhan_t_lo * varadhan_t_top ^ 4 * 1 := by
            ring
      _ ≤ Heat_kernel_envelope_real varadhan_t_lo * varadhan_t_top ^ 4 *
              (Real.exp (varadhan_c / varadhan_t_lo) *
                Real.exp (-(varadhan_c / t))) :=
            mul_le_mul_of_nonneg_left hexp_ineq
              (mul_nonneg hep_nonneg htop4_pos.le)
  linarith

end TheoremaAureum.Towers.YM.PeterWeylHeatVaradhan

-- ===========================================================================
-- Namespace 3: RiemannianGeometry
-- Placeholder distance d_SU3 and SU3 alias for VaradhanStripWidened.
-- ===========================================================================

namespace TheoremaAureum.Towers.YM.RiemannianGeometry

open TheoremaAureum.SU3

/-- SU3 alias — makes `SU3` available unqualified when this namespace is opened. -/
abbrev SU3 := TheoremaAureum.SU3.SU3

/-- Placeholder Riemannian distance on SU(3).
    HONEST CAVEAT: this is a zero-constant stand-in for the genuine
    SU(3) Killing-form chordal distance.  The geometric bound theorems
    in VaradhanStripWidened are conditioned on `d_SU3 x 1 = 0`
    (diagonal hypothesis); with d_SU3 = 0 this is trivially true for
    every x, so those theorems are vacuously satisfied — they are
    structural slots for a future genuine off-diagonal Varadhan argument.
    YM Surface #1 stays OPEN. -/
noncomputable def d_SU3 (_ _ : TheoremaAureum.SU3.SU3) : ℝ := 0

end TheoremaAureum.Towers.YM.RiemannianGeometry
