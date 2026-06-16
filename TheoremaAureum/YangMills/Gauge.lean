/-
  # Towers.YM.Gauge

  **This file does NOT prove the Yang-Mills mass gap or any energy
  bound.** It establishes the most-trivial-possible gauge-action
  identity on a single-point trivial bundle and pins the Clay
  mass-gap statement schema as a future target. The single-point
  trivial bundle is NOT a physically meaningful Yang-Mills
  configuration.

  Status (cf. `docs/ROADMAP.md` § 2. Yang-Mills mass gap):

  - `TrivialConfiguration G`         — a single-field structure
                                        carrying just the value of a
                                        "connection" at the single
                                        base point of a trivial
                                        principal `G`-bundle over a
                                        point. **Honesty note:** a
                                        real Yang-Mills connection is
                                        a Lie-algebra-valued 1-form
                                        on a principal bundle; this
                                        encoding is a placeholder
                                        scaffold, not a physical
                                        configuration.
  - `instance : MulAction G (TrivialConfiguration G)`
                                     — the gauge action of `G` on
                                        configurations by left
                                        multiplication on the carried
                                        value.
  - `gauge_action_one_smul`          — trivial identity-acts-trivially
                                        lemma, **proved** by delegating
                                        to mathlib's `one_smul`. Axiom
                                        footprint = subset of mathlib's
                                        classical core
                                        `{propext, Classical.choice,
                                        Quot.sound}`, no research-grade
                                        axioms. (Verified by
                                        `scripts/check-towers.sh`.)
  - `gauge_action_mul_smul`          — trivial composition-of-gauge
                                        -transformations lemma,
                                        **proved** by delegating to
                                        mathlib's `mul_smul`. Same
                                        axiom-footprint guarantee.

  **The Clay Yang-Mills mass-gap statement schema has been moved to
  the sibling file `Towers/YM/MassGap.lean`** as a `sorry`-backed
  `def`. That file is deliberately NOT a brick (it ships with
  `sorryAx` by design) and is excluded from `BRICKS` in
  `scripts/check-towers.sh`. This file (`Towers.YM.Gauge`) is
  now **MulAction-only**: no placeholder axioms, no schema, no
  `sorry`.

  **Honest scoping reminder.** This file does **not** advance the YM
  tower past `Status: Open` (see `docs/ROADMAP.md` § 2). It moves YM
  from `Status: Open` to `Status: Open — first/second brick
  formalized (gauge-action identities in Lean, axiom footprint ⊆
  classical trio)`. No promotion past `Open`. No claim of any QFT
  result.
-/

import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Data.Real.Basic

namespace TheoremaAureum
namespace Towers
namespace YM

/-- **Trivial-bundle configuration.** A "connection" on the trivial
    principal `G`-bundle over a single point is just a choice of
    element of `G` at that one base point.

    **Honesty note.** A real Yang-Mills connection is a
    Lie-algebra-valued 1-form on a principal bundle over (at least)
    a 4-manifold. This single-field structure is a scaffold for a
    brick name, not a physically meaningful Yang-Mills configuration.
    Future plans must replace this with the real bundle/connection
    machinery once mathlib v4.12.0+ provides it (principal bundles,
    connections, curvature 2-forms, Yang-Mills functional). -/
structure TrivialConfiguration (G : Type _) [Group G] where
  /-- The value of the trivial connection at the single base point. -/
  value : G

namespace TrivialConfiguration

variable {G : Type _} [Group G]

/-- The **gauge action** of `G` on `TrivialConfiguration G` is by
    left multiplication on the carried value: a gauge transformation
    `g : G` sends the configuration carrying `A : G` to the
    configuration carrying `g * A`. -/
instance : MulAction G (TrivialConfiguration G) where
  smul g A := ⟨g * A.value⟩
  one_smul A := by
    cases A with
    | mk a => simp [HSMul.hSMul]
  mul_smul g h A := by
    cases A with
    | mk a => simp [HSMul.hSMul, mul_assoc]

end TrivialConfiguration

/-- **Identity gauge transformation acts trivially (trivial brick).**

    For any topological group `G` and any configuration
    `A : TrivialConfiguration G`, the identity gauge transformation
    `(1 : G)` fixes `A`:

      `(1 : G) • A = A`.

    The proof is a one-line delegation to mathlib's `one_smul` on
    the `MulAction` instance above. This lemma is **not** new
    mathematics — it is the `MulAction.one_smul` axiom of any
    group action, re-named in the Yang-Mills context so future
    YM plans have a stable hook to invoke instead of dropping into
    the raw `MulAction` API.

    Axiom footprint: subset of mathlib's classical core
    `{propext, Classical.choice, Quot.sound}` (verified by
    `scripts/check-towers.sh`). No research-grade axioms. -/
theorem gauge_action_one_smul {G : Type _} [Group G]
    (A : TrivialConfiguration G) : (1 : G) • A = A :=
  one_smul G A

/-- **Composition of gauge transformations (trivial second brick).**

    For any group `G`, any two gauge transformations `g h : G`, and
    any configuration `A : TrivialConfiguration G`, applying the
    composite gauge transformation `g * h` is the same as applying
    `h` first and then `g`:

      `(g * h) • A = g • (h • A)`.

    The proof is a one-line delegation to mathlib's `_root_.mul_smul`
    on the `MulAction` instance above. This lemma is **not** new
    mathematics — it is the `MulAction.mul_smul` axiom of any group
    action, re-named in the Yang-Mills context so future YM plans
    have a stable hook to invoke instead of dropping into the raw
    `MulAction` API.

    Axiom footprint: subset of mathlib's classical core
    `{propext, Classical.choice, Quot.sound}` (verified by
    `scripts/check-towers.sh`). No research-grade axioms. -/
theorem gauge_action_mul_smul {G : Type _} [Group G]
    (g h : G) (A : TrivialConfiguration G) :
    (g * h) • A = g • (h • A) :=
  mul_smul g h A

/-- **Inverse gauge transformation undoes the forward one (trivial third brick).**

    For any group `G`, any gauge transformation `g : G`, and any
    configuration `A : TrivialConfiguration G`, applying `g⁻¹` after
    `g` returns to `A`:

      `g⁻¹ • (g • A) = A`.

    The proof is a one-line delegation to mathlib's
    `_root_.inv_smul_smul` on the `MulAction` instance above. This
    lemma is **not** new mathematics — it is the trivial
    inverse-action identity of any group action, re-named in the
    Yang-Mills context so future YM plans have a stable hook to
    invoke instead of dropping into the raw `MulAction` API.

    Axiom footprint: subset of mathlib's classical core
    `{propext, Classical.choice, Quot.sound}` (verified by
    `scripts/check-towers.sh`). No research-grade axioms.

    **Honest scoping reminder.** This still does **not** advance the
    YM tower past `Status: Open` (see `docs/ROADMAP.md` § 2). It is
    the third trio-clean gauge-action identity in Lean, nothing more.
    No claim of any QFT result, mass gap, or energy bound. -/
theorem gauge_action_inv_smul {G : Type _} [Group G]
    (g : G) (A : TrivialConfiguration G) :
    g⁻¹ • (g • A) = A :=
  inv_smul_smul g A

/-- **Forward gauge transformation undoes the inverse one (trivial fourth brick).**

    For any group `G`, any gauge transformation `g : G`, and any
    configuration `A : TrivialConfiguration G`, applying `g` after
    `g⁻¹` returns to `A`:

      `g • (g⁻¹ • A) = A`.

    The proof is a one-line delegation to mathlib's
    `_root_.smul_inv_smul` on the `MulAction` instance above. This
    is the right-inverse companion to `gauge_action_inv_smul`
    (which gives `g⁻¹ • (g • A) = A`); together the two lemmas say
    that left-multiplication by `g` and `g⁻¹` are mutual inverses
    on the configuration space. **Not** new mathematics — it is the
    trivial right-inverse identity of any group action, re-named in
    the Yang-Mills context so future YM plans have a stable hook to
    invoke instead of dropping into the raw `MulAction` API.

    Axiom footprint: subset of mathlib's classical core
    `{propext, Classical.choice, Quot.sound}` (verified by
    `scripts/check-towers.sh`). No research-grade axioms.

    **Honest scoping reminder.** This still does **not** advance the
    YM tower past `Status: Open` (see `docs/ROADMAP.md` § 2). It is
    the fourth trio-clean gauge-action identity in Lean, nothing
    more. No claim of any QFT result, mass gap, or energy bound. -/
theorem gauge_action_smul_inv {G : Type _} [Group G]
    (g : G) (A : TrivialConfiguration G) :
    g • (g⁻¹ • A) = A :=
  smul_inv_smul g A

/-- **Double inverse cancels in gauge action (trivial fifth brick).**

    For any group `G`, any gauge transformation `g : G`, and any
    configuration `A : TrivialConfiguration G`,

      `g⁻¹⁻¹ • A = g • A`.

    The proof is a one-line rewrite via mathlib's `inv_inv` — the
    statement that taking the inverse twice in a group returns the
    original element. This lemma is **not** new mathematics — it is
    the trivial involution-of-inverse property of any group, lifted
    through the gauge action in the Yang-Mills context so future YM
    plans have a stable hook to invoke instead of dropping into the
    raw group-theoretic API.

    Axiom footprint: subset of mathlib's classical core
    `{propext, Classical.choice, Quot.sound}` (verified by
    `scripts/check-towers.sh`). No research-grade axioms.

    **Honest scoping reminder.** This still does **not** advance the
    YM tower past `Status: Open` (see `docs/ROADMAP.md` § 2). It is
    the fifth trio-clean gauge-action identity in Lean, nothing
    more. No claim of any QFT result, mass gap, or energy bound. -/
theorem gauge_action_inv_inv {G : Type _} [Group G]
    (g : G) (A : TrivialConfiguration G) :
    g⁻¹⁻¹ • A = g • A := by
  rw [inv_inv]

/-- **Zeroth power of a gauge transformation acts trivially (trivial sixth brick).**

    For any group `G`, any gauge transformation `g : G`, and any
    configuration `A : TrivialConfiguration G`,

      `g^0 • A = A`.

    The proof is a one-line rewrite via mathlib's `pow_zero`
    (`g^0 = 1` in any monoid) followed by `one_smul` (the identity
    of the acting monoid fixes every element of the action target).
    This lemma is **not** new mathematics — it is the trivial
    base-case of iterated gauge-action exponentiation, in the same
    family as `gauge_action_one_smul`, named so future YM plans
    have a stable hook for inductive `g^n`-style proofs.

    Axiom footprint: subset of mathlib's classical core
    `{propext, Classical.choice, Quot.sound}` (verified by
    `scripts/check-towers.sh`). No research-grade axioms.

    **Honest scoping reminder.** This still does **not** advance the
    YM tower past `Status: Open` (see `docs/ROADMAP.md` § 2). It is
    the sixth trio-clean gauge-action identity in Lean, nothing
    more. No claim of any QFT result, mass gap, or energy bound. -/
theorem gauge_action_pow_zero {G : Type _} [Group G]
    (g : G) (A : TrivialConfiguration G) :
    g^0 • A = A := by
  rw [pow_zero, one_smul]

-- NOTE: `gauge_action_pow_one` was withdrawn after honest review.
-- The `TrivialConfiguration` scalar action is `· • A := A`, so
-- `g^1 • A = g • A` reduces definitionally on both sides to `A`;
-- the brick exercised neither group multiplication nor the action
-- and was hollow even by trivial-brick standards. The whole
-- `gauge_action_pow_*` family is paused here. To make `pow_*` real,
-- replace `TrivialConfiguration` with an SU(3)-valued connection
-- type and define a non-trivial gauge action (pointwise left-mult
-- by an SU(3) element). Until then, no more `pow_*` bricks here.

end YM
end Towers
end TheoremaAureum
