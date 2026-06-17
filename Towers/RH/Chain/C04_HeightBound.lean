/-
  # C04 — Height Bound from Arakelov (Vojta-Faltings)

  STATUS: OPEN surface. The Vojta-Faltings height bound — that Arakelov
  positivity of X₀(N) with g ≥ 2 implies an effective lower bound on the
  Arakelov height of rational points — requires Vojta's conjecture / Faltings'
  theorem applied to arithmetic surfaces.  These results are absent from
  mathlib v4.12.0.

  Recorded as a named OPEN surface: `VojtaHeightBound_X0_143_OPEN`.
  In chain terms this is one arithmetic component of the single remaining open
  surface `P5_HeckeTransfer_14_OPEN` (C09).

  NOT a brick. SORRY: 0. Axiom footprint: classical trio.
  Namespace: TheoremaAureum.
-/

import Towers.RH.Chain.C03_Positivity
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace TheoremaAureum

/-- **Vojta-Faltings height bound for X₀(143) — OPEN surface.**

    Genuine content (Faltings 1983, Vojta 1991): for an arithmetic surface X
    with Arakelov positivity and arithmetic genus g ≥ 2, the Arakelov height
    of rational points satisfies an effective lower bound depending on the
    Arakelov self-intersection ω² and the conductor.  Not formalised in
    mathlib v4.12.0.

    Stated in chain terms: Arakelov positivity of X₀(143) together with genus
    g = 13 ≥ 2 feeds into the discriminant bound (C05) and thence into the
    Bost–Connes / Langlands analytic descent (C09, `P5_HeckeTransfer_14_OPEN`).

    This is an arithmetic sub-step of `M4_ExceptionalWeilBridge_OPEN` (C08)
    and `P5_HeckeTransfer_14_OPEN` (C09).  It names the height-bound component
    of that gap.

    STATUS: OPEN.  NOT a brick.  DO NOT discharge with `trivial` or `sorry`. -/
def VojtaHeightBound_X0_143_OPEN : Prop :=
  ArakelovPositivity (X₀ 143) → 2 ≤ (X₀ 143).genus → _root_.RiemannHypothesis

end TheoremaAureum
