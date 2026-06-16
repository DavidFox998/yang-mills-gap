/-
# Open Surfaces — Named OPEN hypotheses for yang-mills-gap
#
# Three Prop definitions capturing the OPEN statements that block Surface #1
# (YM mass gap, Clay Millennium problem). None is proved here. Each is a
# Prop that, when supplied as an explicit hypothesis, makes downstream
# theorems sorry-free and classical-trio-only (no sorryAx).
#
# Axiom footprint: propext, Classical.choice, Quot.sound only.
# YM remains Status: Open. No mass-gap / μ > 0 claim is made.
-/

import Towers.YM.Transfer

namespace TheoremaAureum.Towers.YM.Transfer

open MeasureTheory SU3Instances

/-- **Surface 1a — Kotecký–Preiss spectral criterion (OPEN).**

Uniform-in-L spectral gap above vacuum: for β large enough there is gap > 0
so that on the vacuum-orthogonal sector (zero-mean L², i.e. f ⊥ constants)
the transfer operator T_L is an exp(-(β·gap))-contraction:

  ‖T_L L β f‖ ≤ exp(-(β · gap)) · ‖f‖

The missing combinatorial input is the cluster-entropy Peierls bound:
  #{γ : |γ| = n, energy(γ) < ε} ≤ Cⁿ · ε^{α·n}
which makes the KP convergence sum finite at a finite β₀ < ∞.

NOT proved. NOT discharged with sorry.
#print axioms kotecky_preiss_criterion_Surface → [propext, Classical.choice, Quot.sound].
Surface #1 stays OPEN; YM stays Status: Open. -/
def kotecky_preiss_criterion_Surface : Prop :=
  ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ < β →
    ∃ gap : ℝ, 0 < gap ∧
      ∀ (L : ℕ) (f : Lp ℝ 2 (haarN (4 * L ^ 4))),
        (∫ U, f U ∂(haarN (4 * L ^ 4)) = 0) →
          ‖T_L L β f‖ ≤ Real.exp (-(β * gap)) * ‖f‖

/-- **Surface 1b — Trivial-polymer set Haar-null (OPEN).**

For a non-empty polymer γ (a finite set of oriented plaquettes), the set of
link configurations w : Fin (4·L⁴) → SU(3) for which every plaquette of γ
has zero Wilson energy (all plaquette matrices are the identity) has
haarN-measure zero:

  haarN (4·L⁴) {w | polymerEnergy (toGauge L w) γ = 0} = 0

Requires at minimum: (i) NoAtoms haarSU3 (identity non-isolated in SU(3)),
and (ii) a Measure.pi single-coordinate marginal / regular-element argument
for the commuting-variety codimension on small lattices. Both are unproved
in this repo.

NOT proved. NOT discharged with sorry.
#print axioms trivial_polymer_set_null_Surface → [propext, Classical.choice, Quot.sound].
Surface #1 stays OPEN; YM stays Status: Open. -/
def trivial_polymer_set_null_Surface (L : ℕ) [NeZero L]
    (γ : Finset (Lattice 4 L × Fin 4 × Fin 4)) : Prop :=
  haarN (4 * L ^ 4) {w | polymerEnergy (toGauge L w) γ = 0} = 0

/-- **Surface 1c — Polymer activity decay (OPEN, depends on Surface 1b).**

For a non-empty polymer γ, the activity (Haar integral of the heat kernel
restricted to γ) decays to 0 as β → ∞:

  Filter.Tendsto (fun β => polymerActivity L β γ) Filter.atTop (nhds 0)

This follows from trivial_polymer_set_null_Surface via dominated convergence
(Transfer.lean: polymerActivity_tendsto_zero_of_null). It is stated here as
an independent Surface so it can be threaded as an explicit hypothesis without
importing the DCT reduction.

NOT proved independently. NOT discharged with sorry.
#print axioms polymerActivity_tendsto_zero_Surface → [propext, Classical.choice, Quot.sound].
Surface #1 stays OPEN; YM stays Status: Open. -/
def polymerActivity_tendsto_zero_Surface (L : ℕ) [NeZero L]
    (γ : Finset (Lattice 4 L × Fin 4 × Fin 4)) : Prop :=
  Filter.Tendsto (fun β => polymerActivity L β γ)
    Filter.atTop (nhds (0 : ℝ))

end TheoremaAureum.Towers.YM.Transfer
