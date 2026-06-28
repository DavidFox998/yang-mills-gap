# Yang-Mills Tower — Morning Star Project

Classical trio only. No sorry. No native_decide. Mathlib v4.12.0.

Axiom footprint: `{propext, Classical.choice, Quot.sound}`.

## What is here

Machine-checked Lean 4 proofs for the SU(3) lattice Yang-Mills
Kotecky-Preiss coupling-constant tower at β₀ ∈ (2.07, 2.08).

SORRY: 0 across all files. No research-grade axioms. No native_decide.
YM Surface #1 (mass gap): LOCKED OPEN. No Clay claim.

---

## Current state (2026-06-28)

**Unconditional chain:** fully proved up to `w1_weyl_series β₀ < 1/7`.
**Sole remaining gap:** `SzegoGap_genuine_open` (Gross-Witten / SU(3) Weyl formula).
**Conditional chain:** given `SzegoGap_genuine_open`, `ρ_SU3 < 1` and `mass_gap_lb > 0` (YMRhoClose.lean).

---

## Proved unconditionally (0 sorry, classical trio)

| Result | File | Notes |
|--------|------|-------|
| β₀ ∈ (2.07, 2.08) | `Wall256_Scaffold.lean` | Rational enclosure |
| **`PartC_Surface`** ✓ | **`BesselBounds.lean`** | N=5 norm_num, +1.30×10⁻¹⁴ margin |
| **`W1_Numeric_Surface`** ✓ | **`BesselBounds.lean`** | via `bb_part_c` (unconditional) |
| **`w1_weyl_series β₀ < 1/7`** ✓ | **`BesselBounds.lean`** | `bb_w1_weyl_lt` |
| Bessel tsum ≤ det | `BesselBounds.lean` | `TsumDetLe_Surface` |
| log 2 > 2/3 | `KP_Closure.lean` | `log_two_gt_two_thirds_Surface` |
| gap_kp_star = ln 8 > 2 | `KP_Closure.lean` | from log 2 > 2/3 |
| `exp_r_cos_continuous`, `exp_r_cos_pos` | `SzegoGapAvenues.lean` | Continuity + positivity |
| **`JacobiAnger_FormCoeff`** ✓ | **`JacobiAngerAvenue1.lean`** | **ALL 5 sub-steps proved, unconditional** |
| `su3_submodule` closure lemmas | `SU3.lean` | ℝ⁸ anti-Hermitian traceless submodule |
| `haarSU3`, `haarN n` | `SU3Instances.lean` | Genuine Haar measure on SU(3) |
| 8 Gell-Mann generators | `SU3Basis.lean` | `su3_equiv_fin8_def` |
| `dim_cubic_bound` | `WeylDim.lean` | dim_SU3 m n ≤ 8·(m+n+1)³ |
| `PeterWeyl_Summable_SU3` | `PeterWeyl.lean` | ∑ dim²·exp(-βC₂) summable β>0 |
| `wilson_rotateConfig_const_one` | `RotationInvariance.lean` | OS-2 at const-1 |
| **`torusElt_mem_SU3`** ✓ | **`SU3MaximalTorus.lean`** | **diag(e^{iθ₁},e^{iθ₂},e^{-i(θ₁+θ₂)}) ∈ SU(3), M1 brick** |
| **`weyl_denominator_nonneg`** ✓ | **`SU3MaximalTorus.lean`** | **Δ(θ₁,θ₂) ≥ 0, M2 brick** |
| `torusElt_comm`, `torusElt_mul` | `SU3MaximalTorus.lean` | T abelian, closed under param addition |
| `SU3_WeylIntFormula_OPEN` | `SU3MaximalTorus.lean` | Named open surface — Avenue 2 gate |

## Proved conditionally (classical trio, named open hypothesis explicit)

| Result | Hypothesis | File |
|--------|------------|------|
| w1(β₀) < 1/7 | `SzegoGap_genuine_open` | `YMCollection.lean` |
| 14 YM chain surfaces | `SzegoGap_genuine_open` | `YMMasterCombinator.lean` |
| `ρ_SU3 < 1/7 < 1` | `SzegoGap_genuine_open` | `YMRhoClose.lean` |
| `mass_gap_lb > 0` | `SzegoGap_genuine_open` | `YMRhoClose.lean` |
| `∃ Δ > 0, Δ ≤ mass_gap_lb` | `SzegoGap_genuine_open` | `YMRhoClose.lean` |

---

## Jacobi-Anger Avenue 1 — COMPLETE (2026-06-28)

File: `Towers/YM/JacobiAngerAvenue1.lean`

All five sub-steps proved (0 sorry, classical trio):

| Sub-step | Statement | Method |
|----------|-----------|--------|
| B — `InterchangeSumIntegral_OPEN` | series↔integral swap | `integral_tsum` DCT |
| C.1 — `FourierCoeff_Single_OPEN` | `fourierCoeff(fourier m) n = δ_{m,n}` | `fourierBasis.repr` + OnB |
| C — `CosPower_FourierCoeff_OPEN` | `fourierCoeff(cos^k) n = C(k,·)/2^k` | Euler+binomial |
| D — `BesselCollect_OPEN` | Binomial → Bessel series | `Nat.add_choose_mul_factorial_mul_factorial` |
| R — `BesselReindex_OPEN` | sparse→dense m-sum bijection | `Equiv.ofBijective`, m ↦ \|n\|+2m |

Result: `jacobiAnger_proved : JacobiAnger_FormCoeff` — **CLOSED, unconditional**.

---

## YMMasterCombinator — 14 chain surfaces (2026-06-28)

File: `Towers/YM/YMMasterCombinator.lean`

Closes 14 named `_OPEN` surfaces in the YM chain, all conditional on
`SzegoGap_genuine_open`. Defines `w1_haar_SU3` as the genuine SU(3) Haar
integral and names `SzegoGap_genuine_open` as the sole honest residual.

---

## YMRhoClose — ρ_SU3 < 1 (2026-06-28)

File: `Towers/YM/YMRhoClose.lean`

Given `SzegoGap_genuine_open`:

```
h_szego : w1_haar_SU3 β₀ = w1_weyl_series β₀
  + bb_w1_weyl_lt (N=5 Bessel cert, unconditional)
→ ρ_SU3 = w1_haar_SU3 β₀ < 1/7 < 1
→ mass_gap_lb = 1 - ρ_SU3 > 0
→ ∃ Δ > 0, Δ ≤ mass_gap_lb
```

0 sorry, classical trio. `SzegoGap_genuine_open` NOT discharged.

---

## Open surfaces — complete ledger

### Sole remaining YM gap

| Surface | Statement | Barrier |
|---------|-----------|---------|
| `SzegoGap_genuine_open` | `w1_haar_SU3 β₀ = w1_weyl_series β₀` | SU(3) Gross-Witten / Weyl formula absent from Mathlib v4.12.0 |

This is the ONLY open surface blocking the full unconditional chain.
Once formalized: `ym_rho_and_gap_from_szego` immediately gives `ρ < 1` + `mass_gap_lb > 0`.

### SzegoGap — Three Avenues

| Avenue | Status | Barrier |
|--------|--------|---------|
| 1 — JacobiAnger (`fourierCoeff(exp(r·cos·)) n = Iₙ(r)`) | **COMPLETE ✓** | — |
| 2 — WeylIntegration_SU3 (∫_{SU(3)} → torus) | OPEN | SU(3) Weyl formula absent |
| 3 — ToeplitzBessel_Id (torus = Toeplitz det) | TRIVIAL placeholder | Fredholm.det absent |

### Clay / locked-open (invariant — do NOT discharge)

| Surface | Notes |
|---------|-------|
| YM Surface #1 (mass gap) | **LOCKED OPEN** — Clay problem; continuum limit not constructed |
| `kotecky_preiss_criterion` | **INVARIANT-LOCKED** — do not discharge (replit.md) |

---

## Dependency structure (2026-06-28)

```
PartC_Surface (PROVED ✓)
      │
      ▼
w1_weyl_series β₀ < 1/7 (PROVED ✓)     JacobiAnger_FormCoeff (PROVED ✓)
      │                                          │
      │              SzegoGap_genuine_open ←──── │ (closes Avenue 1)
      │              (SOLE OPEN GAP)
      │                    │ (given SzegoGap_genuine_open)
      └────────────────────┘
                     ▼
            ρ_SU3 = w1_haar_SU3 β₀ < 1/7 < 1  (YMRhoClose.lean)
                     │
                     ▼
            mass_gap_lb = 1 - ρ_SU3 > 0
                     │
                     ▼
              YM Surface #1 (LOCKED OPEN — Clay)
```

---

## File structure

```
Towers/YM/          Full KP + Wall256 + JacobiAnger + SU3 chain
KP/                 Standalone KP certificate
lakefile.lean       Mathlib v4.12.0, lean_lib Towers + KP
lean-toolchain      leanprover/lean4:v4.12.0
FOR_CERN.txt        SHA-256 manifest of ALL files in this repository
```

## Reproduce

```bash
lake update
lake exe cache get
lake build
grep -rn 'sorry' Towers/YM/ KP/  # should return nothing
```

## Honesty statement

This repository does **not** claim to solve the Clay Yang-Mills Mass Gap
problem. YM Surface #1 is locked OPEN. No mass gap, no μ > 0, no Clay claim.
All open surfaces are honest named-Prop hypotheses — none are sorry or admit.
