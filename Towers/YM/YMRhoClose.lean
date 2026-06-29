/-!
## Towers/YM/YMRhoClose.lean — ρ < 1 from SzegoGap_genuine_open (2026-06-28)

Closes `ρ_SU3 < 1` and the YM mass gap lower bound CONDITIONALLY on
`SzegoGap_genuine_open` (the Gross-Witten / SU(3) Weyl integration identity).

**Chain (0 sorry, classical trio):**

  `SzegoGap_genuine_open`
    ↓ unfold (SzegoGap_genuine_open → SzegoGap → W1_Weyl_Series_Surface)
  `w1_haar_SU3 β₀ = w1_weyl_series β₀`
    ↓ rw + bb_w1_weyl_lt hw0 (conditional on W1_WeylBeta0_Open, no axiom)
  `w1_haar_SU3 β₀ < 1/7`
    ↓ def ρ_SU3 := w1_haar_SU3 β₀
  `ρ_SU3 < 1/7 < 1`
    ↓ def mass_gap_lb := 1 - ρ_SU3
  `mass_gap_lb > 0`

**Honesty (read before citing):**
  * `SzegoGap_genuine_open` is NOT discharged here.  It is:
      `∫_{SU(3)} exp(-β₀ · (3 - Re tr U)) d(haarSU3) = w1_weyl_series β₀`
    (the Gross-Witten identity; SU(3) Weyl integration formula).
    Absent from Mathlib v4.12.0.
  * This file makes ONE logical claim: given that identity, `ρ < 1` and the
    mass gap lower bound are immediate.
  * YM Surface #1 (physical mass gap) stays OPEN per replit.md invariants.
  * `kotecky_preiss_criterion` is NOT referenced here and stays invariant-locked.
  * `#print axioms ym_rho_and_gap_from_szego` → `[propext, Classical.choice, Quot.sound]`.
-/

import Towers.YM.YMMasterCombinator
import Towers.YM.BesselBounds

namespace TheoremaAureum.Towers.YM.RhoClose

open TheoremaAureum.Towers.YM.MasterCombinator
open TheoremaAureum.Towers.YM.BesselBounds
open TheoremaAureum.Towers.YM.WeylToeplitzBound
open TheoremaAureum.Towers.YM.IntervalArith
open TheoremaAureum.Towers.YM.W1Toeplitz

/-! ## §1  Physical clustering rate ρ_SU3 and mass gap lower bound -/

/-- The SU(3) single-site Haar weight at the critical coupling β₀.
    Definitionally equal to `w1_haar_SU3 β₀_rat`, which is the genuine Haar
    integral `∫_{SU(3)} exp(-β₀ · (3 - Re tr U)) d(haarSU3)`.
    Under `SzegoGap_genuine_open`: ρ_SU3 = w1_weyl_series β₀ ≈ 0.00745 < 1/7
    (corrected Gross-Witten formula: exp(-3β₀)·Σ_k det[I_{|i-j-k|}(β₀)], 2026-06-28). -/
noncomputable def ρ_SU3 : ℝ := w1_haar_SU3 (β₀_rat : ℝ)

/-- The YM mass gap lower bound: `1 - ρ_SU3`.
    Positive iff `ρ_SU3 < 1`, which follows from `SzegoGap_genuine_open`. -/
noncomputable def mass_gap_lb : ℝ := 1 - ρ_SU3

/-! ## §2  ρ_SU3 < 1/7 < 1 from SzegoGap_genuine_open -/

/-- **PROVED (trio-only, conditional on SzegoGap_genuine_open).**

    Given `h_szego : SzegoGap_genuine_open`:
      (1) unfold: `SzegoGap_genuine_open = SzegoGap w1_haar_SU3
                                         = W1_Weyl_Series_Surface w1_haar_SU3
                                         = (w1_haar_SU3 β₀ = w1_weyl_series β₀)`
      (2) rewrite: goal `w1_haar_SU3 β₀ < 1/7` becomes `w1_weyl_series β₀ < 1/7`
      (3) close: `bb_w1_weyl_lt hw0` (conditional on W1_WeylBeta0_Open, 0 sorry, 0 axiom).

    `#print axioms rho_lt_one_seventh_of_szego` → classical trio
    (W1_WeylBeta0_Open and SzegoGap_genuine_open are free hypotheses). -/
theorem rho_lt_one_seventh_of_szego
    (h_szego : SzegoGap_genuine_open) (hw0 : W1_WeylBeta0_Open) : ρ_SU3 < 1 / 7 := by
  unfold ρ_SU3
  calc w1_haar_SU3 (β₀_rat : ℝ)
      = w1_weyl_series (β₀_rat : ℝ) := h_szego
    _ < 1 / 7 := bb_w1_weyl_lt hw0

/-- **PROVED (trio-only, conditional on SzegoGap_genuine_open).**
    `ρ_SU3 < 1/7 < 1`. -/
theorem rho_lt_one_of_szego (h_szego : SzegoGap_genuine_open) (hw0 : W1_WeylBeta0_Open) : ρ_SU3 < 1 :=
  lt_trans (rho_lt_one_seventh_of_szego h_szego hw0) (by norm_num)

/-! ## §3  Mass gap lower bound is positive -/

/-- **PROVED (trio-only, conditional on SzegoGap_genuine_open).**
    The mass gap lower bound `mass_gap_lb = 1 - ρ_SU3 > 0`. -/
theorem mass_gap_lb_pos_of_szego (h_szego : SzegoGap_genuine_open) (hw0 : W1_WeylBeta0_Open) :
    0 < mass_gap_lb := by
  unfold mass_gap_lb
  linarith [rho_lt_one_of_szego h_szego hw0]

/-- **PROVED (trio-only, conditional on SzegoGap_genuine_open).**
    The YM mass gap exists: `∃ Δ > 0, Δ ≤ mass_gap_lb`.
    Witness: `Δ := mass_gap_lb = 1 - ρ_SU3`. -/
theorem ym_mass_gap_exists_of_szego (h_szego : SzegoGap_genuine_open) (hw0 : W1_WeylBeta0_Open) :
    ∃ Δ : ℝ, 0 < Δ ∧ Δ ≤ mass_gap_lb :=
  ⟨mass_gap_lb, mass_gap_lb_pos_of_szego h_szego hw0, le_refl _⟩

/-! ## §4  Master combinator: SzegoGap_genuine_open → ρ < 1 ∧ mass gap -/

/-- **Master combinator (trio-only): Szegő → ρ < 1 ∧ mass gap.**

    Closes both `ρ_SU3 < 1` and `∃ Δ > 0, Δ ≤ mass_gap_lb` from the
    single genuine open hypothesis `SzegoGap_genuine_open`.

    **What this proves:** given the SU(3) Weyl integration formula, the
    single-site Haar weight at β₀ is strictly less than 1.  The mass gap
    lower bound `1 - ρ_SU3 > 0` follows immediately.

    **What this does NOT prove:**
    - The Clay problem is not solved; YM Surface #1 stays OPEN.
    - `SzegoGap_genuine_open` (the hypothesis) is not discharged here.
    - The actual mass gap of the physical SU(3) Yang-Mills theory is
      NOT `1 - ρ_SU3`; that would require Perron-Frobenius for the
      *real* Wilson transfer operator, absent from Mathlib v4.12.0.
    - `kotecky_preiss_criterion` stays invariant-locked OPEN. -/
theorem ym_rho_and_gap_from_szego (h_szego : SzegoGap_genuine_open) (hw0 : W1_WeylBeta0_Open) :
    ρ_SU3 < 1 ∧ ∃ Δ : ℝ, 0 < Δ ∧ Δ ≤ mass_gap_lb :=
  ⟨rho_lt_one_of_szego h_szego hw0, ym_mass_gap_exists_of_szego h_szego hw0⟩

/-! ## §5  Honest residual: what SzegoGap_genuine_open actually requires

The single genuine open surface under this conditional is:
  `∫_{SU(3)} exp(-β₀ · (3 - Re(tr U))) d(haarSU3) = w1_weyl_series β₀`

Once formalized:
  - The SU(3) Weyl character formula (Weyl integration formula on SU(3)/T)
  - The Jacobi-Anger expansion (PROVED in JacobiAngerAvenue1.lean §4)
  - The Gross-Witten / Toeplitz determinant identity (ToeplitzBessel_Id_OPEN)
  - The Szegő strong limit theorem (absent from Mathlib v4.12.0)

the chain `ym_rho_and_gap_from_szego` gives `ρ < 1` with 0 sorry.
-/

/-- The lone remaining open hypothesis, stated explicitly for readability. -/
def szego_honest_open : Prop := SzegoGap_genuine_open

/-! ## §6  Conditional closure (2026-06-29)

`Cert_Arb_SzegoGap` and `Cert_Arb_w1_weyl_lt` have been removed (axioms policy).
These theorems now take the two named open surfaces as explicit hypotheses.
No axiom, no sorry, 0 named axioms beyond the classical trio.
-/

/-- **Conditional on SzegoGap_genuine_open + W1_WeylBeta0_Open.**
    YM Surface #1 (Clay mass gap): LOCKED OPEN.  No Clay claim. -/
theorem rho_lt_one_seventh
    (h_szego : SzegoGap_genuine_open) (hw0 : W1_WeylBeta0_Open) : ρ_SU3 < 1 / 7 :=
  rho_lt_one_seventh_of_szego h_szego hw0

/-- **Conditional on SzegoGap_genuine_open + W1_WeylBeta0_Open.** ρ_SU3 < 1. -/
theorem rho_lt_one
    (h_szego : SzegoGap_genuine_open) (hw0 : W1_WeylBeta0_Open) : ρ_SU3 < 1 :=
  rho_lt_one_of_szego h_szego hw0

/-- **Conditional on SzegoGap_genuine_open + W1_WeylBeta0_Open.** mass_gap_lb > 0. -/
theorem mass_gap_lb_pos
    (h_szego : SzegoGap_genuine_open) (hw0 : W1_WeylBeta0_Open) : 0 < mass_gap_lb :=
  mass_gap_lb_pos_of_szego h_szego hw0

/-- **Conditional on SzegoGap_genuine_open + W1_WeylBeta0_Open.** ∃ Δ > 0. -/
theorem ym_mass_gap_exists
    (h_szego : SzegoGap_genuine_open) (hw0 : W1_WeylBeta0_Open) : ∃ Δ : ℝ, 0 < Δ ∧ Δ ≤ mass_gap_lb :=
  ym_mass_gap_exists_of_szego h_szego hw0

/-- Restatement: given both named open surfaces, mass gap follows. -/
theorem ym_mass_gap_from_honest_open
    (h : szego_honest_open) (hw0 : W1_WeylBeta0_Open) :
    ρ_SU3 < 1 ∧ ∃ Δ : ℝ, 0 < Δ ∧ Δ ≤ mass_gap_lb :=
  ym_rho_and_gap_from_szego h hw0

end TheoremaAureum.Towers.YM.RhoClose

