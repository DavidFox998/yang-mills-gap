# SU(3) Haar Measure Infrastructure for Lean 4 / mathlib v4.12.0

**Author:** David Fox (ORCID 0009-0008-1290-6105)
**Project:** Morning Star / Theorema Aureum 143 — Yang–Mills & Mass Gap

---

## Why this repo exists

These files were built **from scratch** because mathlib v4.12.0 does not
ship the instance stack needed to construct a Haar measure on
`SU(3) = Matrix.specialUnitaryGroup (Fin 3) ℂ`.

Specifically, mathlib v4.12.0 provides `TopologicalSpace` on
`specialUnitaryGroup`, but nothing else — no `Group`, no
`TopologicalGroup`, no `CompactSpace`, no `MeasurableSpace`, no
`BorelSpace`. Without all five of those, `MeasureTheory.Measure.haarMeasure`
cannot elaborate. This repo supplies exactly that missing stack, proved
`sorry`-free with the classical axiom trio `{propext, Classical.choice,
Quot.sound}` only, and then layers the Lie algebra, basis, inner product,
Wilson action, and transfer-matrix infrastructure on top.

Every file is verified by `#print axioms` to depend only on the classical
trio — no research-grade axioms, no `sorry`, no `sorryAx`.

---

## What is here

| File | What it does |
|------|-------------|
| `lean/SU3.lean` | Defines `su(3)` as anti-Hermitian traceless 3×3 complex matrices; proves it is a real `Submodule` (`AddCommGroup`, `Module ℝ`) |
| `lean/SU3Instances.lean` | **The core payload.** Builds `Group`, `TopologicalGroup`, `CompactSpace`, `MeasurableSpace`, `BorelSpace` on `SU(3)`. Defines `haarSU3` and the product measure `haarN n` |
| `lean/SU3Basis.lean` | The 8 anti-Hermitian Gell-Mann generators `iλ₁ … iλ₈`; proves each lies in `su3_submodule`; builds the `Basis (Fin 8) ℝ ↥su3_submodule`; constructs the `InnerProductSpace.Core` via a `LinearEquiv` to `Fin 8 → ℝ` |
| `lean/WilsonAction.lean` | Genuine SU(3) Wilson plaquette action: `wilsonPlaquette`, `plaquetteEnergy := (3 − Re tr P)/3`, `wilsonAction β U` |
| `lean/Transfer.lean` | Transfer-matrix bricks over the real Wilson action; imports `SU3Instances` |
| `lean/ActionInvariance.lean` | Wilson action translation invariance at the Dirac support point `const 1` (OS Axiom 2, translation part) |
| `lean/MeasureInvariance.lean` | Gibbs-measure translation invariance (parameterised form, conditioned on pointwise-invariant observable) |

---

## The compactness problem we solved

`Matrix (Fin 3)(Fin 3) ℂ` carries the **Pi topology** in mathlib but has
no canonical metric (matrices have many norms; mathlib leaves the norm
scoped to avoid diamonds). This means the standard Heine–Borel route
(`Metric.isCompact_of_isClosed_isBounded`, requires `ProperSpace`) is
unavailable.

**Our route:**

1. **Boundedness:** Entries of a unitary matrix satisfy `‖A i j‖ ≤ 1`.
   Proof: from `star A * A = 1`, the `(j,j)` diagonal entry gives
   `∑ₖ ‖A k j‖² = 1`, so each term is `≤ 1`.

2. **Compact ambient:** The poly-disc
   `∏ᵢⱼ Metric.closedBall (0 : ℂ) 1` is compact by
   `isCompact_univ_pi` applied twice (once per `Fin 3` index).
   The Matrix type IS the Pi type, so this applies directly with
   a `Set (Matrix …)` type ascription.

3. **SU(3) is closed:** Preimage of `{1}` under the two continuous maps
   `A ↦ A · star A` and `A ↦ det A`.

4. **SU(3) is compact:** Closed subset of a compact set.
   `IsCompact.of_isClosed_subset` → `isCompact_iff_compactSpace`.

**Key lesson for `SecondCountableTopology`:** `inferInstance` fails for
`SecondCountableTopology ↥SU3` because the instance
`Subtype.secondCountableTopology` is keyed on the `Set` sort-coercion,
but `↥SU3` uses the *Submonoid* sort-coercion. Bridge it manually:

```lean
haveI : SecondCountableTopology (↥SU3) :=
  TopologicalSpace.Subtype.secondCountableTopology
    (SU3 : Set (Matrix (Fin 3) (Fin 3) ℂ))
```

---

## Usage

These files require **Lean 4** and **mathlib v4.12.0**. Add to your
`lakefile.lean` or import directly:

```lean
import SU3Instances  -- gives haarSU3 : MeasureTheory.Measure SU3
import SU3           -- gives su3_submodule : Submodule ℝ (Matrix …)
import SU3Basis      -- gives su3_basis_def : Basis (Fin 8) ℝ ↥su3_submodule
```

The central definition:

```lean
noncomputable def haarSU3 : MeasureTheory.Measure SU3 :=
  MeasureTheory.Measure.haarMeasure ⊤

noncomputable def haarN (n : ℕ) : MeasureTheory.Measure (Fin n → SU3) :=
  MeasureTheory.Measure.pi (fun _ => haarSU3)
```

---

## What is NOT claimed

These files are **infrastructure only**. They do not:

- Prove the Yang–Mills mass gap (`μ > 0`) — that is a Clay Millennium
  problem and remains **OPEN**
- Prove the SU(3) Weyl / Gross–Witten integration formula (absent from
  mathlib v4.12.0)
- Prove any spectral bound or eigenvalue estimate
- Make any `μ > 0`, `Surface #1 closed`, or mass-gap claim

The axiom footprint of every definition in this repo is the classical trio
`{propext, Classical.choice, Quot.sound}`, verified via `#print axioms`.

---

## Background

This work is part of the **Morning Star / Theorema Aureum 143** project,
an attempt to build a formally verified proof tower toward the Clay
Yang–Mills and Mass Gap problem using Lean 4 and mathlib. The larger
tower — including the NS Navier–Stokes tower, the SU(3) cluster expansion
scaffold, the Kotecký–Preiss summability chain, and the BesselBounds
in-Lean interval-arithmetic project — lives in the main project repository.

The SU(3) Haar instance stack here represents the genuine measure-theoretic
foundation that any serious lattice-YM Lean formalization must build before
the Wilson action, transfer operator, or Osterwalder–Schrader axioms can be
stated non-vacuously.

---

## License

MIT. Use freely; attribution appreciated.

---

*Last updated: 2026-06-12*
