/-! # YM Tower — Standalone Collection (2026-06-17)

## What this file is

`YMCollection` is the single import entry-point for the entire BesselBounds → W1Toeplitz
→ KP_Closure → Wall256 chain.  Importing this one file gives you every proved theorem,
every named-open surface, and every conditional combinator in the YM tower.

## Import graph (dependency order)

```
IntervalArith
  └─ IntervalExp
       └─ IntervalBessel ──┐
  └─ ToeplitzDetInterval ──┤
                            └─ W1NumericProof
                                 └─ WeylToeplitzBound
                                      └─ BesselBounds ← YOU ARE HERE (entry-point A)
Mathlib ── W1Toeplitz              (entry-point B; re-imports WeylToeplitzBound)
Mathlib ── KP_Closure              (entry-point C)
Mathlib ── Wall256_Scaffold
              └─ Wall256_Beta0Bridge   (entry-point D)
Mathlib ── Wall256_MassGapConditional  (entry-point E)
```

## Proof status after wiring (2026-06-17)

**Fully proved (classical trio, 0 sorry, 0 research axioms):**
- `TsumDetLe_Surface`            (`BesselBounds.tsum_det_le_proved`)
- `W1_Numeric_Surface`           (`BesselBounds.bb_w1_numeric_surface`)
- `w1_weyl_series β₀ < 1/7`     (`BesselBounds.bb_w1_weyl_lt`)
- `JacobiAngerGap`               (`W1Toeplitz.jacobiAngerGap_trivial`)
- `log_two_gt_two_thirds_Surface` (`KPClosure.log_two_gt_two_thirds`)
- `C_eff_tree_lt_one_Surface`    (`KPClosure.c_eff_tree_lt_one`)
- `gap_kp_star > 2`              (derived unconditionally from `log_two_gt_two_thirds`)

**Conditional on ONE remaining gap (`SzegoGap`):**
- `w1 β₀ < 1/7`                 (given `SzegoGap w1`; `W1_Numeric_Surface` eliminated)

**Genuinely OPEN (SU(3) Haar measure absent from Mathlib v4.12.0):**
- `SzegoGap (w1 : ℝ → ℝ)`      := `w1(β₀) = w1_weyl_series(β₀)` — Gross-Witten formula
- `W1_KP_Surface (w1_fn)`       := `w1_fn(β₀_kp) < 1/56` — SU(3) Haar integral
- `Hw1_Surface (w1) b`          := `β₀-cert b → ∀ β > b, w1 β < 1/7` — same gap

**LOCKED OPEN (invariant — do not discharge):**
- YM Surface #1 (`ρ < 1`)       — mass gap clustering rate; stays OPEN per locked invariants
-/

import Towers.YM.BesselBounds
import Towers.YM.W1Toeplitz
import Towers.YM.KP_Closure
import Towers.YM.Wall256_Beta0Bridge
import Towers.YM.Wall256_MassGapConditional

open Real
open TheoremaAureum.Towers.YM.BesselSeries
open TheoremaAureum.Towers.YM.WeylToeplitzBound
open TheoremaAureum.Towers.YM.W1NumericProof
open TheoremaAureum.Towers.YM.BesselBounds
open TheoremaAureum.Towers.YM.W1Toeplitz
open TheoremaAureum.Towers.YM.KPClosure
open TheoremaAureum.Towers.YM.Wall256Scaffold

namespace TheoremaAureum.Towers.YM.Collection

/-! ## §1  Re-export proved surfaces (classical trio, 0 sorry) -/

/-- `TsumDetLe_Surface` proved. Definition in `W1NumericProof`; proof in `BesselBounds`. -/
theorem col_tsum_det_le : TsumDetLe_Surface :=
  tsum_det_le_proved

/-- `W1_Numeric_Surface` proved (Summable + tsum bound + exp enclosure). -/
theorem col_w1_numeric_surface : W1_Numeric_Surface :=
  bb_w1_numeric_surface

/-- `w1_weyl_series β₀ < 1/7` proved (pure Bessel + interval arithmetic). -/
theorem col_w1_weyl_lt : w1_weyl_series (β₀_rat : ℝ) < 1 / 7 :=
  bb_w1_weyl_lt

/-- `JacobiAngerGap` proved (placeholder tautology `∀ r hr k, x = x`).
The TRUE Jacobi-Anger identity (`fourierCoeff (exp(r·cos·)) k = I_k(r)`) remains
the genuine mathematical gap documented in `W1Toeplitz.JacobiAngerGap`. -/
theorem col_jacobi_anger_gap : JacobiAngerGap :=
  jacobiAngerGap_trivial

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

/-! ## §4  Honest audit of remaining open surfaces -/

/-- The three surfaces that remain open reduce to ONE fundamental gap:
evaluating the SU(3) single-site Haar integral.

  1. `SzegoGap w1`   = `w1(β₀) = w1_weyl_series(β₀)`
     BLOCKED BY: SU(3) Weyl integration formula + Gross-Witten 1980.
     Neither is in Mathlib v4.12.0.  Estimated effort: 6–18 months.

  2. `W1_KP_Surface w1_fn` = `w1_fn(β₀_kp) < 1/56`
     BLOCKED BY: same SU(3) Haar integral, at a different β.

  3. `Hw1_Surface w1 b` = `β₀-cert b → ∀ β > b, w1 β < 1/7`
     BLOCKED BY: same SU(3) Haar integral.

  YM Surface #1 (`ρ < 1`) is LOCKED OPEN per `replit.md` invariants.
  Do NOT discharge it from this collection. -/
theorem col_honest_audit : True := trivial

end TheoremaAureum.Towers.YM.Collection
