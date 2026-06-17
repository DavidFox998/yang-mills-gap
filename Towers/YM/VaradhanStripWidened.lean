/-
================================================================
Towers / YM / VaradhanStripWidened

**One-line summary.** Re-state the strip-form Varadhan-shape upper
bound `Heat_kernel_envelope_real_le_varadhan` against a **wider** strip
`[varadhan_t_lo_widened, varadhan_t_top_widened]` whose interior
contains the original strip `[varadhan_t_lo, varadhan_t_top]`.
Inside the *original* strip the new endpoints differ from the old
by additive padding (`varadhan_t_lo_widened := varadhan_t_lo / 2`,
`varadhan_t_top_widened := varadhan_t_top * 2`), and the existing
bound transports across the inclusion **without** changing the
RHS constants `varadhan_C`, `varadhan_c`.

### Drift / honest scope (locked)

The original Task #156 brief asked for a *true* small-`t`
refinement: extend the strip toward `t = 0⁺` and re-derive the
constants so the bound stays sharp. **That refinement is
mathematically false** in the literal Varadhan shape — `env(t) → +∞`
as `t → 0⁺` while `C · exp(-c/t) / t^4 → 0`, so no positive `(C, c)`
can hold on any neighbourhood of `0`.

What this file ships instead:

  * A pair of wider strip endpoints `varadhan_t_lo_widened`,
    `varadhan_t_top_widened` whose closed interval **strictly
    contains** the original strip (the widened lower endpoint is
    `varadhan_t_lo / 2 = 1/200`, the widened upper is
    `varadhan_t_top * 2 = 200`).
  * Positivity of the widened endpoints and the strict containment.
  * A re-statement of the strip bound on the *original* strip
    carried under the *widened* signature.
  * A genuinely wider upper bound using a retuned amplitude
    `varadhan_C_widened` that covers `[varadhan_t_lo, varadhan_t_top_widened]`.

YM tower stays `Status: Open`. Surface #2 stays OPEN.

### Invariants honored

  * Sorry-free (zero `sorry`).
  * Axiom footprint ⊆ `{propext, Classical.choice, Quot.sound}`.
  * No new defs of `varadhan_C`, `varadhan_c`, or the envelope —
    they remain owned by `PeterWeylHeatVaradhan.lean`.
  * No claim about the small-`t` asymptotic on
    `(0, varadhan_t_lo)`.

================================================================
-/

import Towers.YM.PeterWeylHeatVaradhan

namespace TheoremaAureum
namespace Towers
namespace YM
namespace VaradhanStripWidened

open TheoremaAureum.Towers.YM.PeterWeylHeat
open TheoremaAureum.Towers.YM.PeterWeylHeatVaradhan
open TheoremaAureum.Towers.YM.RiemannianGeometry

/-- **Widened strip lower endpoint.**
    Concrete value `varadhan_t_lo / 2 = 1/200`. Strictly positive but
    strictly less than `varadhan_t_lo`; the widening is a *slot* for a
    future genuine small-`t` refinement, **not** itself a valid lower
    bound for the strip-form Varadhan inequality. -/
noncomputable def varadhan_t_lo_widened : ℝ := varadhan_t_lo / 2

/-- **Widened strip upper endpoint.**
    Concrete value `varadhan_t_top * 2 = 200`. -/
noncomputable def varadhan_t_top_widened : ℝ := varadhan_t_top * 2

/-- The widened lower endpoint is strictly positive. -/
theorem varadhan_t_lo_widened_pos : 0 < varadhan_t_lo_widened := by
  unfold varadhan_t_lo_widened varadhan_t_lo; norm_num

/-- The widened upper endpoint is strictly positive. -/
theorem varadhan_t_top_widened_pos : 0 < varadhan_t_top_widened := by
  unfold varadhan_t_top_widened varadhan_t_top; norm_num

/-- The widened strip strictly contains the original strip on the
left: `varadhan_t_lo_widened < varadhan_t_lo`. -/
theorem varadhan_t_lo_widened_lt : varadhan_t_lo_widened < varadhan_t_lo := by
  unfold varadhan_t_lo_widened varadhan_t_lo; norm_num

/-- The widened strip strictly contains the original strip on the
right: `varadhan_t_top < varadhan_t_top_widened`. -/
theorem varadhan_t_top_lt_widened : varadhan_t_top < varadhan_t_top_widened := by
  unfold varadhan_t_top_widened varadhan_t_top; norm_num

/-- **Strip-form Varadhan-shape upper bound, widened-signature
re-statement.** When `t` lies in the *original* strip
`[varadhan_t_lo, varadhan_t_top]` (necessarily inside the widened
strip), the existing bound from `PeterWeylHeatVaradhan.lean`
applies verbatim — the RHS constants `varadhan_C`, `varadhan_c`
are unchanged.

This is **not** a genuine extension of the valid `t`-range: the
hypotheses are still the original strip bounds. The widened
endpoint defs above are slots for a future refinement, not an
honest claim that the bound holds on the wider window. -/
theorem Heat_kernel_envelope_real_le_varadhan_widened
    {t : ℝ} (ht_lo : varadhan_t_lo ≤ t) (ht_top : t ≤ varadhan_t_top) :
    Heat_kernel_envelope_real t ≤
      varadhan_C * Real.exp (-(varadhan_c / t)) / t ^ 4 :=
  Heat_kernel_envelope_real_le_varadhan ht_lo ht_top

/-! ## Genuine upper-side widening -/

/-- **Retuned Varadhan amplitude for the widened upper side.** Same
shape as `varadhan_C` (owned by `PeterWeylHeatVaradhan.lean`),
but with the strip-top factor `varadhan_t_top ^ 4` replaced by the
*widened* top `varadhan_t_top_widened ^ 4`.

The retuning the algebra forces: to carry `t` all the way up to
`varadhan_t_top_widened` the polynomial factor must use the widened
top, so the amplitude grows by `(varadhan_t_top_widened / varadhan_t_top) ^ 4 = 2^4 = 16`.
Positive because each factor is positive. -/
noncomputable def varadhan_C_widened : ℝ :=
  Heat_kernel_envelope_real varadhan_t_lo *
    varadhan_t_top_widened ^ 4 * Real.exp (varadhan_c / varadhan_t_lo)

/-- The retuned widened amplitude is strictly positive. -/
theorem varadhan_C_widened_pos : 0 < varadhan_C_widened := by
  unfold varadhan_C_widened
  have he : (1 : ℝ) ≤ Heat_kernel_envelope_real varadhan_t_lo :=
    Heat_kernel_envelope_real_ge_one_of_pos varadhan_t_lo_pos
  have hep : (0 : ℝ) < Heat_kernel_envelope_real varadhan_t_lo := by linarith
  have htop4 : (0 : ℝ) < varadhan_t_top_widened ^ 4 :=
    pow_pos varadhan_t_top_widened_pos 4
  exact mul_pos (mul_pos hep htop4) (Real.exp_pos _)

/-- **Strip-form Varadhan-shape upper bound, genuinely extended to
the widened upper side.** For every `t : ℝ` with
`varadhan_t_lo ≤ t ≤ varadhan_t_top_widened`, i.e. `t` ranges over
the *original* lower endpoint up to the *widened* top
`varadhan_t_top_widened = 2 · varadhan_t_top`:
  `Heat_kernel_envelope_real t ≤ varadhan_C_widened · exp(-(varadhan_c / t)) / t^4`.

Unlike `Heat_kernel_envelope_real_le_varadhan_widened` (which merely
re-states the existing bound under the original strip hypotheses),
this brick **really enlarges the valid `t`-window on the upper side**
to `(varadhan_t_top, varadhan_t_top_widened]` and **retunes the RHS
amplitude** to `varadhan_C_widened` to absorb the larger polynomial
factor.

The lower endpoint is **deliberately left at `varadhan_t_lo`**: the
literal small-`t` Varadhan inequality is mathematically false on
`(0, varadhan_t_lo)`.

**Honest scope (locked).** Still a *strip* bound on a bounded
`t`-window, NOT the small-`t` asymptotic on a neighbourhood of `0`.
YM tower stays `Status: Open`; Surface #2 stays OPEN. -/
theorem Heat_kernel_envelope_real_le_varadhan_widened_upper
    {t : ℝ} (ht_lo : varadhan_t_lo ≤ t) (ht_top : t ≤ varadhan_t_top_widened) :
    Heat_kernel_envelope_real t ≤
      varadhan_C_widened * Real.exp (-(varadhan_c / t)) / t ^ 4 := by
  have htpos : 0 < t := lt_of_lt_of_le varadhan_t_lo_pos ht_lo
  have ht4_pos : 0 < t ^ 4 := pow_pos htpos 4
  -- Step 1: antitonicity of the envelope gives `env(t) ≤ env(t_lo)`.
  have hmono :
      Heat_kernel_envelope_real t ≤ Heat_kernel_envelope_real varadhan_t_lo :=
    Heat_kernel_envelope_real_antitone varadhan_t_lo_pos ht_lo
  have he : (1 : ℝ) ≤ Heat_kernel_envelope_real varadhan_t_lo :=
    Heat_kernel_envelope_real_ge_one_of_pos varadhan_t_lo_pos
  have hep_nonneg : 0 ≤ Heat_kernel_envelope_real varadhan_t_lo := by linarith
  have htop4_pos : 0 < varadhan_t_top_widened ^ 4 :=
    pow_pos varadhan_t_top_widened_pos 4
  -- (a) `c/t ≤ c/t_lo` since `0 < t_lo ≤ t` and `c > 0`.
  have hclo : varadhan_c / t ≤ varadhan_c / varadhan_t_lo := by
    rw [div_le_div_iff htpos varadhan_t_lo_pos]
    have := mul_le_mul_of_nonneg_left ht_lo varadhan_c_pos.le
    linarith
  -- (b) Hence `exp(c/t_lo) · exp(-c/t) ≥ exp(0) = 1`.
  have hexp_ineq :
      1 ≤ Real.exp (varadhan_c / varadhan_t_lo) *
            Real.exp (-(varadhan_c / t)) := by
    rw [← Real.exp_add]
    have h0 : (0 : ℝ) ≤ varadhan_c / varadhan_t_lo + -(varadhan_c / t) := by
      linarith
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (varadhan_c / varadhan_t_lo + -(varadhan_c / t)) :=
            Real.exp_le_exp.mpr h0
  -- (c) `t^4 ≤ t_top_widened^4` since `0 ≤ t ≤ t_top_widened`.
  have ht4_le : t ^ 4 ≤ varadhan_t_top_widened ^ 4 :=
    pow_le_pow_left htpos.le ht_top 4
  -- Combine: `env(t_lo) ≤ C_widened · exp(-c/t) / t^4`.
  have hrhs :
      Heat_kernel_envelope_real varadhan_t_lo ≤
        varadhan_C_widened * Real.exp (-(varadhan_c / t)) / t ^ 4 := by
    rw [le_div_iff₀ ht4_pos]
    have hC_eq :
        varadhan_C_widened * Real.exp (-(varadhan_c / t)) =
          Heat_kernel_envelope_real varadhan_t_lo *
            varadhan_t_top_widened ^ 4 *
              (Real.exp (varadhan_c / varadhan_t_lo) *
                Real.exp (-(varadhan_c / t))) := by
      unfold varadhan_C_widened; ring
    rw [hC_eq]
    calc Heat_kernel_envelope_real varadhan_t_lo * t ^ 4
        ≤ Heat_kernel_envelope_real varadhan_t_lo * varadhan_t_top_widened ^ 4 :=
            mul_le_mul_of_nonneg_left ht4_le hep_nonneg
      _ = Heat_kernel_envelope_real varadhan_t_lo * varadhan_t_top_widened ^ 4 * 1 := by
            ring
      _ ≤ Heat_kernel_envelope_real varadhan_t_lo * varadhan_t_top_widened ^ 4 *
            (Real.exp (varadhan_c / varadhan_t_lo) *
              Real.exp (-(varadhan_c / t))) :=
            mul_le_mul_of_nonneg_left hexp_ineq
              (mul_nonneg hep_nonneg htop4_pos.le)
  linarith

/-- **Geometric-form Varadhan-shape upper bound, genuinely extended to
the widened upper side.** For every `t : ℝ` with
`varadhan_t_lo ≤ t ≤ varadhan_t_top_widened` and every `x : SU3` on the
diagonal locus `d_SU3 x 1 = 0`:
  `Heat_kernel_envelope_real t ≤`
    `varadhan_C_widened · exp(-(d_SU3 x 1)^2 / (4·t)) / t^4`.

This is the geometric companion of
`Heat_kernel_envelope_real_le_varadhan_widened_upper`: it carries the
`exp(-d(x,1)² / 4t)` geometric decay factor but **widens the valid
upper `t`-window** from `varadhan_t_top` up to
`varadhan_t_top_widened = 2 · varadhan_t_top`, with the RHS amplitude
**retuned** to `varadhan_C_widened`.

On the diagonal locus `d_SU3 x 1 = 0` the geometric exp factor
collapses to `1`, so the geometric RHS reduces to
`varadhan_C_widened / t^4`, and the strip bound plus `exp(-c/t) ≤ 1`
closes it.

**Task #189 / #210 tripwire — diagonal hypothesis.** The diagonal
hypothesis `hx : d_SU3 x 1 = 0` is retained: with the real
Killing-form chordal `d_SU3`, the off-diagonal case `d_SU3 x 1 > 0`
makes the RHS strictly smaller, which is exactly the open Varadhan /
Molchanov off-diagonal asymptotic. The lower endpoint stays at
`varadhan_t_lo`.

**Honest scope (locked).** Still a *strip* bound on a bounded
`t`-window, NOT the small-`t` asymptotic, and NOT the off-diagonal
Varadhan asymptotic. YM tower stays `Status: Open`; Surface #2 stays
OPEN. -/
theorem Heat_kernel_envelope_real_le_varadhan_geometric_widened_upper
    {t : ℝ} (ht_lo : varadhan_t_lo ≤ t) (ht_top : t ≤ varadhan_t_top_widened)
    (x : SU3) (hx : d_SU3 x (1 : SU3) = 0) :
    Heat_kernel_envelope_real t ≤
      varadhan_C_widened *
        Real.exp (-((d_SU3 x (1 : SU3)) ^ 2 / (4 * t))) / t ^ 4 := by
  have htpos : 0 < t := lt_of_lt_of_le varadhan_t_lo_pos ht_lo
  have ht4_pos : 0 < t ^ 4 := pow_pos htpos 4
  -- Step 1: the upper-widened strip bound (retuned amplitude).
  have hstrip :
      Heat_kernel_envelope_real t ≤
        varadhan_C_widened * Real.exp (-(varadhan_c / t)) / t ^ 4 :=
    Heat_kernel_envelope_real_le_varadhan_widened_upper ht_lo ht_top
  -- Step 2: the geometric exp factor collapses to `1` on the diagonal.
  have hgeom_zero : (d_SU3 x (1 : SU3)) ^ 2 / (4 * t) = 0 := by
    rw [hx]; ring
  have hexp_geom :
      Real.exp (-((d_SU3 x (1 : SU3)) ^ 2 / (4 * t))) = 1 := by
    rw [hgeom_zero, neg_zero, Real.exp_zero]
  -- Step 3: `exp(-(c/t)) ≤ 1` since `c, t > 0`.
  have hcoverpos : 0 ≤ varadhan_c / t :=
    div_nonneg varadhan_c_pos.le htpos.le
  have hexp_le_one :
      Real.exp (-(varadhan_c / t)) ≤ 1 := by
    calc Real.exp (-(varadhan_c / t))
        ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  -- Step 4: turn the geometric RHS into `varadhan_C_widened / t^4` and chain.
  have hVC_pos : 0 < varadhan_C_widened := varadhan_C_widened_pos
  have h_geom_rhs :
      varadhan_C_widened *
          Real.exp (-((d_SU3 x (1 : SU3)) ^ 2 / (4 * t))) / t ^ 4 =
        varadhan_C_widened / t ^ 4 := by
    rw [hexp_geom, mul_one]
  rw [h_geom_rhs]
  have hnum :
      varadhan_C_widened * Real.exp (-(varadhan_c / t)) ≤ varadhan_C_widened := by
    calc varadhan_C_widened * Real.exp (-(varadhan_c / t))
        ≤ varadhan_C_widened * 1 :=
          mul_le_mul_of_nonneg_left hexp_le_one hVC_pos.le
      _ = varadhan_C_widened := mul_one _
  have hstrip_le :
      varadhan_C_widened * Real.exp (-(varadhan_c / t)) / t ^ 4 ≤
        varadhan_C_widened / t ^ 4 := by
    rw [div_le_div_iff ht4_pos ht4_pos]
    nlinarith [hnum, ht4_pos]
  exact le_trans hstrip hstrip_le

end VaradhanStripWidened
end YM
end Towers
end TheoremaAureum
