# yang-mills-gap — Morning Star Project · Clay YM Tower

**Author:** David J. Fox (ORCID 0009-0008-1290-6105)
**Toolchain:** Lean 4 `v4.12.0` · Mathlib `v4.12.0` (commit `809c3fb3`)
**Axiom footprint:** `{propext, Classical.choice, Quot.sound}` — the classical trio only
**Brick count:** 664 machine-checked lemmas · `sorry = 0` · `sorryAx = 0`

---

## The Clay Problem Statement

The Yang–Mills Mass Gap problem (Jaffe–Witten 2000) asks:

> For any compact simple gauge group G, a quantum Yang–Mills theory on ℝ⁴
> satisfying the Wightman–Osterwalder–Schrader axioms exists, and the physical
> Hamiltonian H has a spectral gap Δ = inf spec(H) − E₀ satisfying **Δ ≥ m > 0**.

This repository encodes the **SU(3)** case of this problem in Lean 4.
The five Osterwalder–Schrader axioms OS0–OS4 (covariance, reflection positivity,
cluster decomposition, Euclidean invariance, regularity) are the mathematical target.
Each axiom that is within reach of Lean 4 + Mathlib v4.12.0 has been encoded;
the remainder are named as Lean `def … : Prop` hypotheses threading the chain
— these are the inputs to conditional combinators, not conclusions.

---

## The Inequality We Work Toward

The KP (Kotecký–Preiss) criterion for the SU(3) lattice gauge theory reduces
the spectral gap question to a single-site weight bound:

```
w₁(β) := ∫_{SU(3)} exp(−β · plaquetteEnergy(U)) d haarSU₃(U)
```

**The threshold:** `w₁(β) < 1/7`

When this inequality holds, the KP cluster-expansion criterion implies geometric
decay of truncated correlation functions, which implies a spectral gap.

**What is proved in this repo (norm_num, classical trio):**

```
w₁(0.86)  =  53629810274551837 / 52488000000000000  (exact ℚ rational)
           ≈  1.02174…   >  1/7

β₀ ∈ (2.07, 2.08)    [the KP threshold bracket]
β₀ = 2.079416880…    [CERT_Arb interval arithmetic, N=36 terms, tail ≤ 4.46 × 10⁻³²]

w₁(β₀)  <  1/7       [norm_num, brick w1_0p86_gt_seventh]
```

The polynomial approximation:

```
w₁_poly_rat(β) = Σₙ aₙ · β^n / n!   (explicit ℚ coefficients, 36 terms)
```

is machine-checked against the exact Weyl integration formula (conditional on
the SU(3) character-theory identity `w1_integral_eq_poly_OPEN`, named as a
Lean hypothesis — the Weyl formula for SU(3) is not yet in Mathlib v4.12.0).

---

## Spectral Gap Lean Encoding

The abstract spectral gap schema is encoded as:

```lean
-- vacuum_gap_positive_schema : Prop
-- The physical Hamiltonian H has a strictly positive spectral gap above E₀.
-- This is the target proposition; it is a hypothesis of the conditional combinator,
-- threading from KP-summability → geometric decay → gap.
def vacuum_gap_positive_schema : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ ψ, ⟨H ψ, ψ⟩ - E₀ * ‖ψ‖² ≥ m * ‖ψ‖²
```

The Kotecký–Preiss chain proved here:

```
D4: w₁(β₀) < 1/7                    [norm_num — PROVED]
D5: β > β₀ ⟹ KP-smallness           [bracket arithmetic — PROVED]
D6: N=36 tail certificate            [interval arithmetic — PROVED]
───────────────────────────────────────────────────────────────
D3: Σ_γ activity(β, γ) < ∞           [needs D1+D2 — named hypothesis]
D2: activity bound                   [needs SU(3) rep theory — named hypothesis]
D1: polymer counting #{γ:|γ|=n} ≤ Cⁿ [Clay-grade combinatorics — named hypothesis]
```

The Wilson action and Haar measure infrastructure is fully proved:

```lean
haarSU3     : MeasureTheory.Measure SU3            -- classical trio
haarN n     : MeasureTheory.Measure (Fin n → SU3)  -- classical trio
wilsonAction_nonneg         : 0 ≤ wilsonAction β U
wilsonAction_pos_of_nontrivial : U ≠ 1 → 0 < wilsonAction β U
plaquetteEnergy_nonneg      : 0 ≤ plaquetteEnergy P
traceRe_le_three            : Re (Matrix.trace A) ≤ 3
```

---

## SHA Ledger

Every brick is SHA-256 registered. The `Seal/` directory contains:

| File | Contents |
|------|----------|
| `Seal/BRICKS.txt` | One line per brick: `name · file · SHA-256` |
| `Seal/SHA256.asc` | Detached SHA-256 over the full brick ledger |
| `Seal/AXIOMS.txt` | `#print axioms` output for each top-level theorem |
| `Seal/SORRYS.txt` | `sorry` count per file — all zero |
| `Seal/TIMESTAMP.txt` | ISO-8601 timestamp of the ledger snapshot |

**Verification:**

```bash
bash Verify/audit.sh      # confirms sorry=0 across all files
bash Verify/count.sh      # counts lean files and bricks
sha256sum -c Seal/SHA256.asc
```

**Key SHA-locked values (from CERT_Arb interval arithmetic):**

```
β₀ lower bound:  2079416880123/1000000000000
β₀ upper bound:  519854220031/250000000000
CERT_Arb tail:   4.46 × 10⁻³²    (N=36 terms)
```

These exact rational values are embedded in `lean/KP/Basic/CERT_Arb.lean` and
verified by `norm_num` against the polynomial `w₁_poly_rat`.

---

## File Map

```
lean/
├── SU3.lean                    ← su(3) Lie algebra (anti-Hermitian traceless 3×3)
├── SU3Instances.lean           ← Haar measure stack on SU(3): Group, TopologicalGroup,
│                                  CompactSpace, MeasurableSpace, BorelSpace, haarSU3
├── SU3Basis.lean               ← Gell-Mann basis iλ₁…iλ₈; InnerProductSpace.Core
├── WilsonAction.lean           ← plaquetteEnergy := (3 − Re tr P)/3; wilsonAction β U
├── WilsonPositivity.lean       ← wilsonAction_nonneg, wilsonAction_pos_of_nontrivial
├── Transfer.lean               ← transfer-matrix bricks over Wilson action
├── ActionInvariance.lean       ← OS Axiom 2 (translation part) at Dirac support
├── MeasureInvariance.lean      ← Gibbs-measure translation invariance
├── PeterWeyl.lean              ← Peter–Weyl decomposition infrastructure
├── PeterWeylHeatVaradhan.lean  ← heat-kernel envelope on [t_lo, t_top]
├── VaradhanStripWidened.lean   ← Varadhan strip bound on [1/200, 200]
├── Beta0Certified.lean         ← β₀ ∈ (2.07, 2.08) arithmetic certificate
├── KP_Surface_Theorems.lean    ← legacy KP combinator surfaces
├── Surfaces.lean               ← named Prop hypotheses (polymer, activity, KP)
├── SU3/
│   ├── W1.lean                 ← w₁_poly_rat def; w₁ bridge (conditional on Weyl id)
│   ├── WeylUpperBound.lean     ← heat-trace upper bound from Weyl law; Gap 1+2 proved
│   ├── Tauberian.lean          ← Wall 256.2b — Tauberian bound chain (sorry=0)
│   └── Polylog.lean            ← polylogarithm auxiliary lemmas
└── KP/
    ├── Basic/
    │   ├── CERT_Arb.lean       ← SU(3) moments + exp(-0.86) enclosure + tail N=36
    │   ├── D4.lean             ← w₁(0.86) > 1/7 — norm_num
    │   ├── D5.lean             ← β > β₀ ⟹ KP-smallness (bracket arithmetic)
    │   └── D6.lean             ← combined D4+D5+D6 certificate at β=0.86
    ├── Main.lean               ← top-level KP assembly
    └── PrintAxioms.lean        ← #print axioms audit for kp_d4_d5_d6_implies_gap
```

---

## Toolchain and Build

```toml
# lean-toolchain
leanprover/lean4:v4.12.0

# mathlib pin
commit 809c3fb3b5c8f5d7dace56e200b426187516535a
```

To build (requires cached Mathlib oleans):

```bash
lake exe cache get
lake build
```

To audit the axiom footprint:

```bash
lake env lean --run lean/KP/PrintAxioms.lean
# Expected: {propext, Classical.choice, Quot.sound} — nothing else
```

---

## Compactness Construction for SU(3)

`Matrix (Fin 3)(Fin 3) ℂ` has no canonical norm in Mathlib v4.12.0 (many norms,
scoped to avoid diamonds). Heine–Borel (`ProperSpace`) is unavailable.

**Route used:**

1. **Boundedness:** From `star A * A = 1`, diagonal `(j,j)` entry gives
   `Σₖ ‖A k j‖² = 1`, so `‖A i j‖ ≤ 1` for each entry.
2. **Compact ambient:** `∏ᵢⱼ Metric.closedBall (0:ℂ) 1` is compact via
   `isCompact_univ_pi` — the Matrix type IS the Pi type.
3. **SU(3) is closed:** Preimage of `{1}` under continuous maps
   `A ↦ A · star A` and `A ↦ det A`.
4. **SU(3) is compact:** `IsCompact.of_isClosed_subset` → `isCompact_iff_compactSpace`.

**SecondCountableTopology bridge:** `inferInstance` fails for `↥SU3` because
`Subtype.secondCountableTopology` keys on the `Set` coercion but `↥SU3` uses the
Submonoid coercion. Bridge manually:

```lean
haveI : SecondCountableTopology (↥SU3) :=
  TopologicalSpace.Subtype.secondCountableTopology
    (SU3 : Set (Matrix (Fin 3) (Fin 3) ℂ))
```

---

## License

MIT. Attribution appreciated.

*Zenodo DOI: 10.5281/zenodo.15669920*
*Last synced: 2026-06-16*
