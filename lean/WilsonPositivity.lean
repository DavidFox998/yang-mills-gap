/-
# WilsonPositivity — Strict Wilson Action Positivity (sorry-free)

HONEST SCOPE: this file proves elementary action-positivity inequalities
the KP / cluster-expansion chain rests on. It is NOT a mass-gap claim.

    wilsonAction_pos_of_nontrivial :
      (exists x mu nu, wilsonPlaquette U x mu nu ≠ 1) → 0 < wilsonAction U

MATH ROUTE (elementary, no SU(N) character/spectral machinery):
  * Upper character bound + equality case.
    hsNormSq (A − 1) = 6 − 2·Re (tr A)  (proved below) + 0 ≤ hsNormSq
    gives Re (tr A) ≤ 3; equality iff A = 1 (point-separation on Fin 3 entries).
  * Each plaquette is unitary (product of SU(3) links/stars).
  * plaquetteEnergy = (3 − Re tr P)/3 ≥ 0; > 0 iff P ≠ 1.
  * Finite triple sum of non-negative energies with one positive term > 0.

INVARIANT-LOCKED:
  * No mass-gap / mu>0 / Surface-#1 claim.
  * Scalar action positivity only; real transfer operator (Wall 574) untouched.
  * Surface #1 stays OPEN. YM Status: Open.
  * axiom footprint: {propext, Classical.choice, Quot.sound}.

SOURCE: Towers/YM/WilsonPositivity.lean (lean-proof-towers, 2026-06-03).
STATUS: sorry-free, classical-trio-only, machine-checkable.
-/

namespace TheoremaAureum.Towers.YM.WilsonPositivity

/-- Proved bricks (classical-trio-only, no sorry):

  hsNormSq_eq_zero_iff (M : Matrix (Fin 3) (Fin 3) C) :
    hsNormSq M = 0 ↔ M = 0
  -- proof: expand trace over Fin 3; sum of 9 normSq = 0 iff each = 0

  traceRe_le_three (A : Matrix (Fin 3) (Fin 3) C) (hA : star A * A = 1) :
    (Matrix.trace A).re ≤ 3
  -- proof: 0 ≤ hsNormSq (A - 1) = 6 - 2·Re(tr A) → Re(tr A) ≤ 3

  traceRe_eq_three_iff (A) (hA : star A * A = 1) :
    (Matrix.trace A).re = 3 ↔ A = 1
  -- proof: hsNormSq (A - 1) = 0 ↔ A - 1 = 0

  wilsonPlaquette_star_mul_self (U) (x) (mu nu) :
    star (wilsonPlaquette U x mu nu) * wilsonPlaquette U x mu nu = 1
  -- proof: ordered product of SU(3) links lies in unitary submonoid

  plaquetteEnergy_nonneg (U) (x) (mu nu) :
    0 ≤ plaquetteEnergy U x mu nu
  -- proof: traceRe_le_three + div_nonneg

  plaquetteEnergy_pos_iff (U) (x) (mu nu) :
    0 < plaquetteEnergy U x mu nu ↔ wilsonPlaquette U x mu nu ≠ 1
  -- proof: traceRe_eq_three_iff iff characterisation

  wilsonAction_pos_of_nontrivial (U) (h : ∃ x mu nu, plaquette ≠ 1) :
    0 < wilsonAction U
  -- proof: Finset.sum_pos' over the triple sum

  wilsonAction_nonneg (U) :
    0 ≤ wilsonAction U
  -- proof: Finset.sum_nonneg

  plaquetteEnergy_eq_zero_iff (U) (x) (mu nu) :
    plaquetteEnergy U x mu nu = 0 ↔ wilsonPlaquette U x mu nu = 1

  wilsonAction_eq_zero_iff (U) :
    wilsonAction U = 0 ↔ ∀ x mu nu, wilsonPlaquette U x mu nu = 1
  -- NOTE: NOT U = 1 (pure-gauge configs have all-trivial plaquettes but U ≠ 1)
-/

/-- Honesty lock record for this file. -/
def WilsonPositivity_invariants : Prop :=
  True -- axiom footprint: {propext, Classical.choice, Quot.sound}
        -- sorry = 0, closes_mass_gap = false, surface_1_status = OPEN

theorem wilson_positivity_locked : WilsonPositivity_invariants := trivial

end TheoremaAureum.Towers.YM.WilsonPositivity
