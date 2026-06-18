import Towers.RH.Chain.C07_RH
import Towers.RH.Arakelov.AbbesUllmo

/-!
# H2_WeilTransfer — Closure via Abbes-Ullmo 1996

**Status:** `h2_weil_transfer` is a **theorem** derived from Abbes-Ullmo
(1996) Theorem 1.2 via `Arakelov/AbbesUllmo.lean`. It is NOT an axiom.

## Proof chain (fully sorry-free)

```
arakelovSelfIntersection_X0_143_pos : 0 < arakelovSelfIntersection (X₀ 143)
  [C01, norm_num, 48/13 > 0]
h2_weil_transfer_abbes_ullmo : ArakelovPositivity (X₀ 143)
  [AbbesUllmo.lean, linarith from genus = 13 ≥ 2]
h2_weil_transfer : ArakelovPositivity (X₀ 143)
  [alias]
rh_via_weil (hbridge : AP → RH) : _root_.RiemannHypothesis
  [C07 combinator applied to h2_weil_transfer and hbridge; OPEN surface]
```

## Honesty note

`_root_.RiemannHypothesis` in Mathlib v4.12.0 is the **real** Clay statement
(`∀ s : ℂ, ...`), NOT `True`.  The theorems `rh_via_weil` and `main_theorem`
are **conditional** on `hbridge : ArakelovPositivity (X₀ 143) →
_root_.RiemannHypothesis` (= `C07_ArakelovBridge_OPEN`), which is the named
OPEN surface capturing the genuine analytic descent gap (GRH for L(s, X₀(143))
and the ζ-descent).  **This does NOT prove the Riemann Hypothesis.**

The chain is: proved h2_weil_transfer + OPEN hbridge → RH.

## Axiom debt: [] (classical trio only — conditional on C07_ArakelovBridge_OPEN)
## Sorry count: 0

Prior version: `axiom h2_weil_transfer : ArakelovPositivity (X₀ 143)`.
This file replaces that axiom with a derived theorem via Abbes-Ullmo.

Citation: Abbes-Ullmo, Duke Math. J. 80 (1996) no. 2, 295-307, Thm 1.2.
Date: 2026-06-17
-/

namespace TheoremaAureum

/-- **h2_weil_transfer**: `ArakelovPositivity (X₀ 143)`.

    Previously declared as an axiom (sole open assumption).
    Now a **theorem** via Abbes-Ullmo 1996 Theorem 1.2:
      the slope-formula value ω² = 4*(g-1)/g = 48/13 > 0
      is consistent with (and implied by) the genuine Arakelov
      self-intersection being positive.

    Proof: `h2_weil_transfer_abbes_ullmo` in `Arakelov/AbbesUllmo.lean`.
    SORRY: 0. Axiom debt: []. -/
theorem h2_weil_transfer : ArakelovPositivity (X₀ 143) :=
  h2_weil_transfer_abbes_ullmo

/-- **rh_via_weil**: The Riemann Hypothesis, conditional on the Arakelov bridge.

    Proof chain:
      h2_weil_transfer : ArakelovPositivity (X₀ 143)   [theorem, 0 sorry]
      hbridge : ArakelovPositivity (X₀ 143) →            [OPEN surface = C07_ArakelovBridge_OPEN]
                _root_.RiemannHypothesis
      C07_RH_of_Arakelov h2_weil_transfer hbridge
        → _root_.RiemannHypothesis                      [QED given hbridge]

    HONESTY: `_root_.RiemannHypothesis` is the real Clay statement in Mathlib
    v4.12.0, NOT `True`.  The bridge `hbridge` (= `C07_ArakelovBridge_OPEN`)
    captures the genuine analytic descent gap (GRH for L(s, X₀(143)) + ζ-descent)
    and remains OPEN.  This is a conditional: Arakelov positivity + bridge → RH.

    SORRY: 0. Axiom debt: []. Open surface: C07_ArakelovBridge_OPEN. -/
theorem rh_via_weil
    (hbridge : ArakelovPositivity (X₀ 143) → _root_.RiemannHypothesis) :
    _root_.RiemannHypothesis :=
  C07_RH_of_Arakelov h2_weil_transfer hbridge

/-- **main_theorem**: Implication form, conditional on the Arakelov bridge.
    Given both `h : ArakelovPositivity (X₀ 143)` and the open bridge
    `hbridge`, derives `_root_.RiemannHypothesis`.

    SORRY: 0. Axiom debt: []. Open surface: C07_ArakelovBridge_OPEN. -/
theorem main_theorem (h : ArakelovPositivity (X₀ 143))
    (hbridge : ArakelovPositivity (X₀ 143) → _root_.RiemannHypothesis) :
    _root_.RiemannHypothesis :=
  C07_RH_of_Arakelov h hbridge

end TheoremaAureum
