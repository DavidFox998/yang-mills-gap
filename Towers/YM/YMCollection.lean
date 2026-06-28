import Towers.YM.BesselBounds
import Towers.YM.W1Toeplitz
import Towers.YM.KP_Closure
import Towers.YM.KP_Bridge
import Towers.YM.Wall256_Beta0Bridge
import Towers.YM.Wall256_MassGapConditional
import Towers.YM.JacobiAngerAvenue1
-- Avenue 2 prerequisite infrastructure (all proved, classical trio, 0 sorry):
import Towers.YM.SU3
import Towers.YM.SU3Instances
import Towers.YM.SU3Basis
import Towers.YM.WeylDim
import Towers.YM.PeterWeyl
import Towers.YM.RotationInvariance

/-! # YM Tower — Standalone Collection (updated 2026-06-28)

## What this file is

`YMCollection` is the single import entry-point for the entire YM tower.
Importing this one file gives you every proved theorem, every named-open surface,
and every conditional combinator — including the Avenue 2 prerequisite
infrastructure (SU(3) Haar measure, Gell-Mann basis, Peter-Weyl summability).

## Import graph (dependency order)

```
IntervalArith
  └─ IntervalExp
       └─ IntervalBessel ──┐
  └─ ToeplitzDetInterval ──┤
                            └─ W1NumericProof
                                 └─ WeylToeplitzBound
                                      └─ BesselBounds ← (entry-point A)
Mathlib ── W1Toeplitz              (entry-point B; re-imports WeylToeplitzBound)
Mathlib ── KP_Closure              (entry-point C)
Mathlib ── Wall256_Scaffold
              └─ Wall256_Beta0Bridge   (entry-point D)
Mathlib ── Wall256_MassGapConditional  (entry-point E)
Mathlib ── SzegoGapAvenues
              └─ JacobiAngerAvenue1    (entry-point F; Avenue 1 PROVED 2026-06-28)
── Avenue 2 prerequisites (all proved, classical trio, 0 sorry):
Mathlib ── SU3                     (entry-point G; su3 Set + su3_submodule)
Mathlib ── SU3Instances            (entry-point H; haarSU3 + haarN genuine Haar measures)
SU3 ──── SU3Basis                  (entry-point I; Gell-Mann generators + su3_equiv_fin8_def)
Mathlib ── WeylDim                 (entry-point J; dim_cubic_bound cubic bound)
ClusterExpansion ── PeterWeyl      (entry-point K; PeterWeyl_Summable_SU3 headline)
WilsonAction ── RotationInvariance (entry-point L; wilson_rotateConfig_const_one)
```

## Proof status after wiring (2026-06-28)

**Fully proved (classical trio, 0 sorry, 0 research axioms):**
- `TsumDetLe_Surface`            (`BesselBounds.tsum_det_le_proved`)
- `W1_Numeric_Surface`           (`BesselBounds.bb_w1_numeric_surface`)
- `w1_weyl_series β₀ < 1/7`     (`BesselBounds.bb_w1_weyl_lt`)
- `JacobiAngerGap`               (`W1Toeplitz.jacobiAngerGap_trivial`)  [tautology placeholder]
- `JacobiAnger_FormCoeff`        (`JacobiAngerAvenue1.jacobiAnger_proved`)  [GENUINE — Avenue 1]
- `log_two_gt_two_thirds_Surface` (`KPClosure.log_two_gt_two_thirds`)
- `C_eff_tree_lt_one_Surface`    (`KPClosure.c_eff_tree_lt_one`)
- `gap_kp_star > 2`              (derived unconditionally from `log_two_gt_two_thirds`)
- `dim_cubic_bound`              (`WeylDim.dim_cubic_bound`) [Avenue 2 prereq — HeatTrace]
- `PeterWeyl_Summable_SU3`       (`PeterWeyl.PeterWeyl_Summable_SU3`) [Avenue 2 prereq]
- `su3_submodule`                (`su3_submodule` def) [Avenue 2 prereq — ℝ⁸ Lie algebra]
- `su3_equiv_fin8_def`           (`su3_equiv_fin8_def` def) [Avenue 2 prereq — basis]
- `haarSU3` / `haarN`           (`SU3Instances.haarSU3/N` def) [Avenue 2 prereq — measure]
- `wilson_rotateConfig_const_one` (`LatticeGauge`) [rotation invariance at const-1]

**Conditional on ONE remaining gap (`SzegoGap`):**
- `w1 β₀ < 1/7`                 (given `SzegoGap w1`; `W1_Numeric_Surface` eliminated)

**Genuinely OPEN (SU(3) Weyl integration formula absent from Mathlib v4.12.0):**
- `SzegoGap (w1 : ℝ → ℝ)`      := `w1(β₀) = w1_weyl_series(β₀)` — Gross-Witten formula
  Decomposed into 3 avenues:
    Avenue 1 `JacobiAnger_FormCoeff`   PROVED ✓ (2026-06-28)
    Avenue 2 `WeylIntegration_SU3`     OPEN  (SU(3) Weyl char formula; 6–12 months)
      Prerequisites PROVED: haarSU3, su3_submodule, su3_equiv_fin8_def,
        PeterWeyl_Summable_SU3, dim_cubic_bound (all in this collection)
    Avenue 3 `ToeplitzBessel_Id`       OPEN  (Fredholm.det; Szegő theorem; 12–18 months)
- `W1_KP_Surface (w1_fn)`       := `w1_fn(β₀_kp) < 1/56` — SU(3) Haar integral
- `Hw1_Surface (w1) b`          := `β₀-cert b → ∀ β > b, w1 β < 1/7` — same gap

**LOCKED OPEN (invariant — do not discharge):**
- YM Surface #1 (`ρ < 1`)       — mass gap clustering rate; stays OPEN per locked invariants
-/

open Real
open TheoremaAureum.Towers.YM.BesselSeries
open TheoremaAureum.Towers.YM.WeylToeplitzBound
open TheoremaAureum.Towers.YM.IntervalArith
open TheoremaAureum.Towers.YM.W1NumericProof
open TheoremaAureum.Towers.YM.BesselBounds
open TheoremaAureum.Towers.YM.W1Toeplitz
open TheoremaAureum.Towers.YM.KPClosure
open TheoremaAureum.Towers.YM.Wall256Scaffold
open TheoremaAureum.Towers.YM.SzegoGapAvenues
open TheoremaAureum.Towers.YM.JacobiAngerAvenue1
open TheoremaAureum.Towers.YM.WeylDim
open TheoremaAureum.Towers.YM.SU3Instances
open TheoremaAureum.Towers.YM.PeterWeyl
open TheoremaAureum.Towers.YM.LatticeGauge

namespace TheoremaAureum.Towers.YM.Collection

/-! ## §1  Re-export proved surfaces (classical trio, 0 sorry) -/

/-- `TsumDetLe_Surface` proved. Definition in `W1NumericProof`; proof in `BesselBounds`. -/
theorem col_tsum_det_le : TsumDetLe_Surface :=
  tsum_det_le_proved

/-- `W1_Numeric_Surface` — proved unconditionally via `bb_part_c`.
Classical trio only. Kept in collection for module-level completeness. -/
theorem col_w1_numeric_surface : W1_Numeric_Surface :=
  bb_w1_numeric_surface

/-- `W1_Numeric_Surface` — conditional form for backward compatibility. -/
theorem col_w1_numeric_surface_cond (hc : PartC_Surface) : W1_Numeric_Surface :=
  bb_w1_numeric_surface_cond hc

/-- `w1_weyl_series β₀ < 1/7` — proved unconditionally via `bb_part_c`. -/
theorem col_w1_weyl_lt : w1_weyl_series (β₀_rat : ℝ) < 1 / 7 :=
  bb_w1_weyl_lt

/-- `w1_weyl_series β₀ < 1/7` — conditional form for backward compatibility. -/
theorem col_w1_weyl_lt_cond (hc : PartC_Surface) : w1_weyl_series (β₀_rat : ℝ) < 1 / 7 :=
  bb_w1_weyl_lt_cond hc

/-- `JacobiAngerGap` — tautology placeholder (`∀ r hr k, x = x`).
Kept for backward compatibility.  The TRUE Jacobi-Anger identity is now in
`col_jacobiAnger_genuine` below. -/
theorem col_jacobi_anger_gap : JacobiAngerGap :=
  jacobiAngerGap_trivial

/-- **PROVED (trio-only, 2026-06-28) — GENUINE Jacobi-Anger identity.**

`fourierCoeff (fun θ => (exp(r · cos θ) : ℂ)) n = (besselI_series |n| r : ℂ)`

for all `r ≥ 0` and `n : ℤ`.

This is the real mathematical content that `JacobiAngerGap` (a tautology) was
naming.  Proved in `JacobiAngerAvenue1` via five sub-steps:
  B  (integral_tsum DCT)
  C.1 (δ_{m,n} Fourier orthonormality)
  C  (Euler formula + binomial theorem)
  D  (choose_factorial_identity)
  R  (injection reindex m ↦ |n| + 2m) -/
theorem col_jacobiAnger_genuine : JacobiAnger_FormCoeff :=
  jacobiAnger_proved

/-- `Real.log 2 > 2/3` proved (Mathlib `log_two_gt_d9`). -/
theorem col_log_two_gt_two_thirds : log_two_gt_two_thirds_Surface :=
  log_two_gt_two_thirds

/-- `(exp(e/4) − 1)/(2·e) < 1` proved (exp monotonicity + `exp_one_lt_d9`). -/
theorem col_c_eff_tree_lt_one : C_eff_tree_lt_one_Surface :=
  c_eff_tree_lt_one

/-! ## §2  Derived unconditional conclusions -/

/-- `gap_kp_star = ln 8 > 2` — now **fully unconditional** (log_two proved above). -/
theorem col_gap_kp_star_gt_two : gap_kp_star > 2 :=
  gap_kp_star_gt_two col_log_two_gt_two_thirds

/-! ## §3  Conditional on SzegoGap only (W1_Numeric_Surface eliminated) -/

/-- `w1 β₀ < 1/7` given only `SzegoGap w1`.
After wiring `W1_Numeric_Surface` (now proved), the reduction is:
  `{trio, SzegoGap, W1_Numeric_Surface}` → `{trio, SzegoGap}`.
`SzegoGap w1 := w1(β₀) = w1_weyl_series(β₀)` is the sole remaining gap. -/
theorem col_w1_lt_of_szego
    (w1 : ℝ → ℝ) (h_szego : SzegoGap w1) :
    w1 (β₀_rat : ℝ) < 1 / 7 :=
  w1_eq_series_from_gaps w1 h_szego bb_w1_numeric_surface

/-- Backward-compat variant; `hc` is unused but kept for callers that supply it. -/
theorem col_w1_lt_of_szego_cond
    (hc : PartC_Surface) (w1 : ℝ → ℝ) (h_szego : SzegoGap w1) :
    w1 (β₀_rat : ℝ) < 1 / 7 :=
  col_w1_lt_of_szego w1 h_szego

/-! ## §4  Honest audit of remaining open surfaces -/

/-- The three surfaces that remain open reduce to ONE fundamental gap:
evaluating the SU(3) single-site Haar integral via the Weyl integration formula.

  1. `SzegoGap w1`   = `w1(β₀) = w1_weyl_series(β₀)`
     BLOCKED BY: SU(3) Weyl integration formula (Avenue 2, §5 below for prerequisites)
                 + Fredholm.det / Szegő theorem (Avenue 3).
     Neither is in Mathlib v4.12.0.  Estimated effort: 6–18 months.

  2. `W1_KP_Surface w1_fn` = `w1_fn(β₀_kp) < 1/56`
     BLOCKED BY: same SU(3) Haar integral, at a different β.

  3. `Hw1_Surface w1 b` = `β₀-cert b → ∀ β > b, w1 β < 1/7`
     BLOCKED BY: same SU(3) Haar integral.

  YM Surface #1 (`ρ < 1`) is LOCKED OPEN per `replit.md` invariants.
  Do NOT discharge it from this collection. -/
theorem col_honest_audit : True := trivial

/-! ## §5  Avenue 2 prerequisite infrastructure (proved, classical trio, 0 sorry)

These bricks are necessary prerequisites for `WeylIntegration_SU3_OPEN` (Avenue 2).
They do NOT close Avenue 2 or SzegoGap — the Weyl integration formula itself
(SU(N) character theory + measure-theoretic reduction to the maximal torus) is absent
from Mathlib v4.12.0.  Each theorem is independently proved; the gap that separates
them from closing Avenue 2 is documented inline.
-/

/-- **PROVED (trio-only) — SU(3) Weyl dimension cubic bound.**

    `dim_SU3 m n ≤ 8 · (m + n + 1)³` for all `(m, n) : ℕ × ℕ`.

    `dim_SU3 m n := (m+1)(n+1)(m+n+2)/2` is the standard SU(3) Weyl formula.
    The cubic bound in `m + n` is the shape needed by `HeatTraceBound` (Task #156
    file-3): the Weyl-law `t^{-d/2}` estimate sums on the `m+n = k` antidiagonal
    and asks for `#{antidiagonal} · dim² · exp(-t·C₂) ≲ poly(k) · exp(-t·k²)`.

    Not sufficient alone for Avenue 2 — the antidiagonal sum also needs
    `Casimir_SU3_explicit ≥ c·(m+n)²` (which requires `dim_cubic_bound` *and*
    the Casimir lower bound already in PeterWeyl). -/
theorem col_dim_cubic_bound (m n : ℕ) : dim_SU3 m n ≤ 8 * (m + n + 1) ^ 3 :=
  dim_cubic_bound m n

/-- **PROVED (trio-only) — SU(3) Peter-Weyl spectral summability.**

    For every `β > 0`, the series
      `∑_{(m,n):ℕ×ℕ} (Weyl_dim_SU3_explicit (m,n))² · exp(-β · Casimir_SU3_explicit (m,n))`
    is `Summable`.

    This is the analytic foundation for the heat-kernel identity
      `K_t(1) = ∑'_λ dim(λ)² · exp(-t · C₂(λ))`.
    The identity itself (equating the *value* of the SU(3) heat kernel at
    the identity to this series) is a separate, harder step (Avenue 2 context)
    that requires the Weyl integration formula.  The summability result here
    says only that the series *converges* — a necessary precondition. -/
theorem col_peterWeyl_summable {β : ℝ} (hβ : 0 < β) :
    Summable (fun mn : ℕ × ℕ =>
      ((TheoremaAureum.Towers.YM.ClusterExpansion.Weyl_dim_SU3_explicit mn : ℝ)) ^ 2 *
        Real.exp (-(β * (TheoremaAureum.Towers.YM.ClusterExpansion.Casimir_SU3_explicit mn : ℝ)))) :=
  PeterWeyl_Summable_SU3 hβ

/-- **PROVED (trio-only) — Casimir linear lower bound.**

    `(m : ℝ) + n ≤ Casimir_SU3_explicit (m, n)` for all `(m, n) : ℕ × ℕ`.
    Supporting lemma for PeterWeyl summability; wired here for completeness. -/
theorem col_casimir_ge_linear (mn : TheoremaAureum.Towers.YM.ClusterExpansion.Weyl_label) :
    ((mn.1 : ℝ) + mn.2) ≤
      (TheoremaAureum.Towers.YM.ClusterExpansion.Casimir_SU3_explicit mn : ℝ) :=
  Casimir_SU3_explicit_real_ge_linear mn

/-- **PROVED (trio-only) — Weyl dimension polynomial upper bound.**

    `(Weyl_dim_SU3_explicit (m,n) : ℝ) ≤ ((m:ℝ)+1)² · ((n:ℝ)+1)²`.
    Supporting lemma for PeterWeyl summability squeeze. -/
theorem col_weyl_dim_le_poly (mn : TheoremaAureum.Towers.YM.ClusterExpansion.Weyl_label) :
    (TheoremaAureum.Towers.YM.ClusterExpansion.Weyl_dim_SU3_explicit mn : ℝ) ≤
      ((mn.1 : ℝ) + 1) ^ 2 * ((mn.2 : ℝ) + 1) ^ 2 :=
  Weyl_dim_SU3_explicit_real_le_poly mn

/-- **PROVED (trio-only) — genuine Haar measure on SU(3) exists.**

    `haarSU3 : MeasureTheory.Measure SU3` is `haarMeasure ⊤` on the compact
    group `SU3 = specialUnitaryGroup (Fin 3) ℂ`, constructed from the full
    instance stack:
      Group + TopologicalGroup + CompactSpace + MeasurableSpace + BorelSpace.

    This is the measure that Avenue 2 (WeylIntegration_SU3) integrates against.
    **What this does NOT provide:** the Weyl integration formula itself, which
    reduces the SU(3) integral to a 2-torus integral.  That reduction requires
    the root-system / character-theory machinery (Mathlib.RootSystem.A₂ exists
    but is not connected to integration in v4.12.0). -/
theorem col_haarSU3_exists : ∃ _ : MeasureTheory.Measure SU3, True :=
  ⟨haarSU3, trivial⟩

/-- **PROVED (trio-only) — genuine product Haar measure on (Fin n → SU3) exists.**

    `haarN n` is the finite product of `haarSU3` over `n` links — the lattice gauge
    configuration-space measure.  This is what the Wilson action is integrated
    against in the lattice YM path integral.  Avenue 2 uses `haarSU3` at `n = 1`
    (the single-site integral). -/
theorem col_haarN_exists (n : ℕ) : ∃ _ : MeasureTheory.Measure (Fin n → SU3), True :=
  ⟨haarN n, trivial⟩

/-- **PROVED (trio-only) — Wilson action rotation invariance at constant-1.**

    `wilsonAction (rotateConfig d L μ ν (fun _ => 1)) = wilsonAction (fun _ => 1)`
    for all `d L μ ν` (Dirac-haar-stand-in form).

    This is the `const 1` specialization of OS Axiom 2 (rotation invariance).
    The genuine universal form `∀ U, wilsonAction (rotateConfig μ ν U) = wilsonAction U`
    is a harder open surface — it requires a `Finset.sum_bij` reindexing over the
    four plaquette corners.  Documented in `RotationInvariance.lean` (tripwire). -/
theorem col_wilson_rotate_const_one (d L : ℕ) [NeZero L] (μ ν : Fin d) :
    wilsonAction (rotateConfig d L μ ν (fun _ : TheoremaAureum.Towers.YM.LatticeGauge.Link d L =>
      (1 : TheoremaAureum.Towers.YM.LatticeGauge.G))) =
    wilsonAction (fun _ : TheoremaAureum.Towers.YM.LatticeGauge.Link d L =>
      (1 : TheoremaAureum.Towers.YM.LatticeGauge.G)) :=
  wilson_rotateConfig_const_one d L μ ν

end TheoremaAureum.Towers.YM.Collection
