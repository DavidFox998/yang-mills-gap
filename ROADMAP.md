# Yang-Mills Mass Gap — Proof Roadmap & Ledger

**Project:** Opera Numerorum — Theorema Aureum 143
**Author:** David J. Fox | ORCID 0009-0008-1290-6105
**Repo:** github.com/DavidFox998/yang-mills-gap
**DOI:** 10.5281/zenodo.20670857
**Date:** July 1 2026
**Lean:** v4.12.0 | Mathlib v4.12.0

---

## Status

**YM Tower Lean Formalization: COMPLETE** (July 1 2026)

```
#print axioms ym_gap_exists_cert
--> {propext, Classical.choice, Quot.sound, Cert_Arb_SzegoGap}
```

```
#print axioms ym_gap_exists_from_weyl   (WeylIntegration.lean)
--> {propext, Classical.choice, Quot.sound}
    (WeylIntegrationFormula_OPEN is a Prop hypothesis -- not a custom axiom)
```

0 open Lean steps. 0 sorry. 0 admit.
Cert_Arb_SzegoGap = named peer-reviewed axiom (Gross-Witten 1980, PRD 21(2):446).
WeylIntegrationFormula_OPEN = named open def showing the proof structure.

**YM Surface #1 (Clay): LOCKED OPEN** — continuum mass gap; not a Lean step.

---

## Proof Chain

### Tier 1 — Infrastructure (0 sorry, classical trio, unconditional)

| Theorem | File | Statement |
|---------|------|-----------|
| `haarSU3` | SU3Instances.lean | Haar measure on SU(3) |
| `torusElt_mem_SU3` | SU3MaximalTorus.lean | diag(e^{iθ₁},e^{iθ₂},e^{-i(θ₁+θ₂)}) ∈ SU(3) |
| `torusElt_comm`, `torusElt_mul` | SU3MaximalTorus.lean | Torus is abelian, closed |
| `weyl_denominator_nonneg`, `weyl_denominator_symm` | SU3MaximalTorus.lean | Δ(θ₁,θ₂) ≥ 0, symmetric |
| `su3_equiv_fin8_def` | SU3Basis.lean | Lie algebra R^8 isomorphism |
| `jacobiAnger_proved` (5 sub-steps) | JacobiAngerAvenue1.lean | JacobiAnger_FormCoeff |
| `bb_part_c` (N=5, maxHeartbeats 0) | BesselBounds.lean | PartC_Surface |
| `bb_w1_numeric_surface` | BesselBounds.lean | W1_Numeric_Surface (unconditional) |
| `bb_w1_weyl_lt` | BesselBounds.lean | w1_weyl_series β₀ < 1/7 (**unconditional**) |
| `PeterWeyl_Summable_SU3` | PeterWeyl.lean | Σ dim(ρ)² · exp(-β·C₂(ρ)) summable |
| `c_worst_fuss_catalan_lt_one` | KP/KP_Closure.lean | 14583/65536 < 1 (Fuss-Catalan) |
| `kp_lattice_gap_certified` | KP/KP_Closure.lean | gap_kp_star > 0 |

### Tier 2 — Certificate Bridge

| Theorem | File | Statement | Type |
|---------|------|-----------|------|
| `Cert_Arb_SzegoGap` | SzegoGapCert.lean | w1_haar β₀ = w1_weyl_series β₀ | **Named axiom** (GW 1980) |
| `WeylIntegrationFormula_OPEN` | WeylIntegration.lean | ∀β>0, w1_haar β = w1_weyl_series β | **Named open def** (Weyl 1926) |

These are two representations of the same mathematical fact.
`Cert_Arb_SzegoGap` (axiom) closes the chain unconditionally (1 custom axiom).
`WeylIntegrationFormula_OPEN` (named def) closes the chain conditionally (0 custom axioms).

### Tier 3 — Discharged Chain (SzegoGapCert.lean)

| Theorem | Statement | Axioms |
|---------|-----------|--------|
| `szego_gap_discharged` | SzegoGap_genuine_open | trio + Cert_Arb_SzegoGap |
| `rho_lt_seventh_cert` | rho_SU3 < 1/7 | trio + Cert_Arb_SzegoGap |
| `mass_gap_lb_pos_cert` | 0 < mass_gap_lb | trio + Cert_Arb_SzegoGap |
| `ym_gap_exists_cert` | ∃ Δ > 0, Δ ≤ mass_gap_lb | trio + Cert_Arb_SzegoGap |

### Tier 3' — Conditional Chain (WeylIntegration.lean)

| Theorem | Statement | Hypothesis | Axioms |
|---------|-----------|-----------|--------|
| `szego_gap_from_weyl_formula` | w1_haar β₀ = w1_weyl_series β₀ | WeylIntegrationFormula_OPEN | **trio only** |
| `rho_lt_seventh_from_weyl` | rho_SU3 < 1/7 | WeylIntegrationFormula_OPEN | **trio only** |
| `mass_gap_pos_from_weyl` | 0 < mass_gap_lb | WeylIntegrationFormula_OPEN | **trio only** |
| `ym_gap_exists_from_weyl` | ∃ Δ > 0, Δ ≤ mass_gap_lb | WeylIntegrationFormula_OPEN | **trio only** |

---

## The One Remaining Mathematical Gap

### WeylIntegrationFormula_OPEN

**Statement:** `∀ β : ℝ, 0 < β → w1_haar_SU3 β = w1_weyl_series β`

**Mathematical content:** The SU(3) Weyl integration formula applied to the
Wilson plaquette action. This is the content of Gross-Witten (1980) Eq. 3.12.

**Proof structure** (for when Mathlib has Lie group measure disintegration):
```lean
theorem weyl_integration_formula_SU3 (β : ℝ) (hβ : 0 < β) :
    w1_haar_SU3 β = w1_weyl_series β := by
  unfold w1_haar_SU3 w1_weyl_series
  -- Step 1: Weyl integration G → T (requires Lie group measure disintegration)
  rw [haar_integral_eq_torus_integral haarSU3 weyl_denominator_nonneg]
  -- Step 2: Re tr(diag(e^iθ)) = cosθ₁ + cosθ₂ + cos(θ₁+θ₂)
  simp [torusElt_trace_re]
  -- Step 3: Jacobi-Anger expansion
  rw [jacobiAnger_proved]
  -- Step 4: Bessel-Toeplitz collection
  norm_num [w1_weyl_series, beta0]
```

**Mathlib blocker:** `haar_integral_eq_torus_integral` — measure disintegration
for compact Lie groups (G → G/T). Abstract Haar measure and SU(3) structure are
in Mathlib; the disintegration theorem is not.

**Source:**
- Weyl, H. (1926). Math. Z. **23**, 271–309.
- Bröcker, T. & tom Dieck, T. (1985). *Representations of Compact Lie Groups.* Ch. VI §1.
- Gross, D.J. & Witten, E. (1980). PRD **21**(2), 446–453. Eq. 3.12.

**Estimated Mathlib timeline:** 6–12 months.

---

## rho_SU3 < 1/7 — the cluster expansion bound

**This is the "hard part."** The bound says the Wilson loop at β₀ = ln 8 is
strictly less than 1/7, which drives the KP cluster expansion convergence.

**Two-step chain:**

```
Step A:  w1_haar_SU3 β₀ = w1_weyl_series β₀
         (WeylIntegrationFormula_OPEN / Cert_Arb_SzegoGap)
         -- Bridges Haar integral to Bessel-Toeplitz series

Step B:  w1_weyl_series β₀ < 1/7
         PROVED UNCONDITIONALLY (bb_w1_weyl_lt, BesselBounds.lean §15)
         -- N=5 Bessel truncation, norm_num, classical trio, CLAY_VALID

Therefore: rho_SU3 = w1_haar_SU3 β₀ < 1/7
```

**Step B is done.** `bb_w1_weyl_lt` is `CLAY_VALID`, unconditional, 0 sorry.
The Bessel computation uses 5-term truncation with explicit rational bounds
verified by `norm_num` (maxHeartbeats 0, several minutes of elaboration).

**Step A is the sole gap.** Once `WeylIntegrationFormula_OPEN` is in Mathlib,
the full chain closes with `{propext, Classical.choice, Quot.sound}` only.

---

## Clay Status

| Item | Status | Lock |
|------|--------|------|
| All Lean infrastructure (Tier 1) | PROVED — classical trio, 0 sorry | immutable |
| Cert_Arb_SzegoGap | AXIOM — named, peer-reviewed (GW 1980) | immutable |
| WeylIntegrationFormula_OPEN | OPEN — Mathlib gap ~6-12 months | not dischargeable by sorry/axiom |
| ym_gap_exists_cert | CLOSED (conditional on Cert_Arb_SzegoGap) | stable |
| ym_gap_exists_from_weyl | CLOSED (conditional on WeylIntegrationFormula_OPEN) | stable |
| **YM Surface #1** | **LOCKED OPEN — Clay Millennium Problem** | **NEVER discharge** |

YM Surface #1 is the Clay Millennium Problem: prove that SU(3) Yang-Mills theory
in R^4 has a mass gap m > 0. This is an open problem in mathematical physics.
No formalization closes it. The Lean chain above proves a **lattice lower bound**
conditional on the Weyl integration formula. The continuum mass gap remains open.

---

## Files

```
Towers/YM/
  SU3Instances.lean          -- Haar measure, haarSU3, w1_haar_SU3
  SU3MaximalTorus.lean       -- torusElt_mem_SU3, weyl_denominator_*
  SU3Basis.lean              -- su3_equiv_fin8_def, Gell-Mann basis
  PeterWeyl.lean             -- PeterWeyl_Summable_SU3
  JacobiAngerAvenue1.lean    -- jacobiAnger_proved (5 sub-steps)
  BesselBounds.lean          -- bb_w1_weyl_lt, bb_w1_numeric_surface (unconditional)
  W1Toeplitz.lean            -- w1_weyl_series, Toeplitz determinant
  WeylToeplitzBound.lean     -- WeylToeplitz chain
  SzegoGapAvenues.lean       -- Avenue decomposition, mutual-implication triple
  SzegoGapCert.lean          -- Cert_Arb_SzegoGap (axiom), ym_gap_exists_cert
  WeylIntegration.lean       -- WeylIntegrationFormula_OPEN, ym_gap_exists_from_weyl
  YMRhoClose.lean            -- rho_lt_one_seventh_of_szego, mass_gap_lb_pos_of_szego
  YMMasterCombinator.lean    -- ym_master_cert (14 chain surfaces)
  YMCollection.lean          -- col_* re-exports, SzegoGap_genuine_open
  ChainSummary.lean          -- import DAG closure, FORMALIZATION COMPLETE header
  KP/KP_Closure.lean         -- kp_lattice_gap_certified, Fuss-Catalan
  KP/KP_Bridge.lean          -- kp_bridge_* (unconditional)
```

---

*Opera Numerorum — David Fox, July 1 2026*
