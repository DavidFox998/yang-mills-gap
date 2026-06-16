/-
# KP Surface Theorems — sorry-free, classical-trio-only pass-throughs
#
# Each theorem takes the corresponding *_Surface hypothesis (the named-open
# Prop from Towers.YM.Surfaces) and returns it. The open content is explicit,
# typed, and threaded as a hypothesis rather than hidden behind sorry.
#
# #print axioms for every theorem here reports only:
#   [propext, Classical.choice, Quot.sound]
# No sorryAx. No sorry. No admit. No new axioms.
#
# YM remains Status: Open. Surface #1 stays OPEN.
# These theorems do NOT prove the mass gap.
-/

import Towers.YM.Surfaces

namespace TheoremaAureum.Towers.YM.Transfer

open MeasureTheory SU3Instances

/-- **Kotecký–Preiss criterion — sorry-free pass-through.**

Given the named-open hypothesis kotecky_preiss_criterion_Surface
(the spectral-gap statement for T_L on vacuum-orthogonal L²),
this theorem re-states it identically. The proof is the hypothesis h.

Honest status: the KP spectral gap is OPEN. This theorem names the gap
without closing it. Surface #1 stays OPEN; YM stays Status: Open.

#print axioms: [propext, Classical.choice, Quot.sound]. -/
theorem kotecky_preiss_criterion
    (h : kotecky_preiss_criterion_Surface) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ < β →
      ∃ gap : ℝ, 0 < gap ∧
        ∀ (L : ℕ) (f : Lp ℝ 2 (haarN (4 * L ^ 4))),
          (∫ U, f U ∂(haarN (4 * L ^ 4)) = 0) →
            ‖T_L L β f‖ ≤ Real.exp (-(β * gap)) * ‖f‖ := h

/-- **Trivial-polymer set null — sorry-free pass-through.**

Given the named-open hypothesis trivial_polymer_set_null_Surface L γ
(the Haar-null fibre statement for non-empty polymer γ),
this theorem re-states it identically. The proof is the hypothesis h.

Honest status: the null-set claim requires NoAtoms haarSU3 + marginal
argument, both unproved. Surface #1 stays OPEN; YM stays Status: Open.

#print axioms: [propext, Classical.choice, Quot.sound]. -/
theorem trivial_polymer_set_null (L : ℕ) [NeZero L]
    (γ : Finset (Lattice 4 L × Fin 4 × Fin 4)) (_hγ : γ ≠ ∅)
    (h : trivial_polymer_set_null_Surface L γ) :
    haarN (4 * L ^ 4) {w | polymerEnergy (toGauge L w) γ = 0} = 0 := h

/-- **Polymer activity decay — sorry-free pass-through.**

Given the named-open hypothesis polymerActivity_tendsto_zero_Surface L γ
(the β → ∞ decay of the polymer activity),
this theorem re-states it identically. The proof is the hypothesis h.

Honest status: the decay follows from trivial_polymer_set_null_Surface via
DCT (Transfer.lean: polymerActivity_tendsto_zero_of_null), but that chain
itself is unproved. Surface #1 stays OPEN; YM stays Status: Open.

#print axioms: [propext, Classical.choice, Quot.sound]. -/
theorem polymerActivity_tendsto_zero (L : ℕ) [NeZero L]
    (γ : Finset (Lattice 4 L × Fin 4 × Fin 4)) (_hγ : γ ≠ ∅)
    (h : polymerActivity_tendsto_zero_Surface L γ) :
    Filter.Tendsto (fun β => polymerActivity L β γ)
      Filter.atTop (nhds (0 : ℝ)) := h

end TheoremaAureum.Towers.YM.Transfer
