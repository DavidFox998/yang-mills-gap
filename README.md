# Yang-Mills Tower — Morning Star Project

Classical trio only. No sorry. No native_decide. Mathlib v4.12.0.

Axiom footprint: `{propext, Classical.choice, Quot.sound}`.

## What is here

Machine-checked Lean 4 proofs for the SU(3) lattice Yang-Mills
Kotecky-Preiss coupling-constant tower at β₀ ∈ (2.07, 2.08).

SORRY: 0 across all files. No research-grade axioms. No native_decide.
YM Surface #1 (mass gap): LOCKED OPEN. No Clay claim.

---

## Proved unconditionally (0 sorry, classical trio)

| Result | File | Notes |
|--------|------|-------|
| β₀ ∈ (2.07, 2.08) | `Wall256_Scaffold.lean` | Rational enclosure, `Beta0Certified` predicate |
| Bessel tsum enclosure tsum ≤ det | `BesselBounds.lean` | `TsumDetLe_Surface` proved |
| log 2 > 2/3 | `KP_Closure.lean` | `log_two_gt_two_thirds_Surface` |
| (exp(e/4)−1)/(2e) < 1 | `KP_Closure.lean` | `C_eff_tree_lt_one_Surface` |
| gap_kp_star = ln 8 > 2 | `KP_Closure.lean` | **Unconditional** (from log 2 > 2/3) |
| 107/756 < 1/7 | `W1Toeplitz.lean` | Rational arithmetic |

## Proved conditionally (classical trio, named open hypothesis explicit)

| Result | Hypothesis required | File |
|--------|---------------------|------|
| W1 numeric bound w1_weyl_series β₀ < 1/7 | `PartC_Surface` | `BesselBounds.lean` |
| `W1_Numeric_Surface` (w1 ≤ 107/756) | `PartC_Surface` | `BesselBounds.lean` |
| w1(β₀) < 1/7 | `PartC_Surface` + `SzegoGap` | `YMCollection.lean` |

`PartC_Surface` is a **named open surface** (see below) — these results are
NOT unconditional bricks.

---

## Open surfaces — complete ledger

All surfaces below are named `def … : Prop` — not `axiom`, not `sorry`,
not a `True`-stub. Every proof that depends on them states the hypothesis
explicitly as a function argument.

### Computational gap (ℚ arithmetic, Lean kernel tactics)

| Surface | Statement | Barrier |
|---------|-----------|---------|
| `PartC_Surface` | `exp_beta0_interval.hi * (finite_hi_sum + tail_ub) < 1/7` | `decide` stalls on `Rat.instDecidableLe`; `norm_num` cannot eval 51-term `Finset.sum`; `native_decide` works (~4-5 min, GMP) but adds `Lean.reduceTrust` — non-trio. Margin ≈ 3.86×10⁻⁷. |

### SU(3) Haar measure gaps (Mathlib v4.12.0)

| Surface | Statement | Barrier |
|---------|-----------|---------|
| `SzegoGap (w1 : ℝ → ℝ)` | `w1(β₀) = w1_weyl_series(β₀)` | SU(3) Weyl integration formula + Gross-Witten 1980 formula absent from Mathlib v4.12.0. Estimated effort: 6–18 months. |
| `W1_KP_Surface (w1_fn)` | `w1_fn(β₀_kp) < 1/56` | SU(3) Haar integral at the KP threshold β — same blocker as SzegoGap. |
| `Hw1_Surface (w1 b)` | `β₀-cert b → ∀ β > b, w1 β < 1/7` | SU(3) Haar integral in β-neighbourhood — same blocker. |

### Jacobi-Anger placeholder

| Surface | Statement | Notes |
|---------|-----------|-------|
| `JacobiAngerGap` | placeholder tautology `∀ r hr k, x = x` | The true gap is `fourierCoeff (exp(r·cos·)) k = I_k(r)` (Jacobi-Anger identity). The named def is proved trivially (`jacobiAngerGap_trivial`) as an honest placeholder; the real identity is absent from Mathlib v4.12.0. |

### Clay / locked-open surfaces (invariant — do NOT discharge)

| Surface | Statement | Notes |
|---------|-----------|-------|
| YM Surface #1 (`ρ < 1`) | Mass-gap clustering rate | **LOCKED OPEN** — continuum limit not constructed; do not discharge from any combinator. |
| `kotecky_preiss_criterion_Surface` | Real KP integral transfer `T_L` | **INVARIANT-LOCKED OPEN** — stays open in `ClusterExpansion.lean` per project invariants. |
| `MassGap_YM4_Clay_Surface T` | Clay 4D SU(3) mass gap | **LOCKED OPEN** — requires continuum quantum field theory not formalised in Mathlib. |

---

## Dependency structure (proved chain)

```
PartC_Surface (OPEN)          SzegoGap (OPEN)
      │                              │
      ▼                              │
W1_Numeric_Surface (conditional)     │
      │                              │
      └──────────────────────────────┘
                     │
                     ▼
            w1(β₀) < 1/7  (conditional on both)
                     │
                     ▼
           KP_Closure: gap_kp_star > 2  ◄── log 2 > 2/3 (PROVED)
                     │
                     ▼
              Wall256_Scaffold (conditional combinator)
```

The unconditional chain terminates at `gap_kp_star > 2`.
Closing `PartC_Surface` and `SzegoGap` would extend the unconditional
chain through the full KP criterion.

---

## File structure

```
Towers/YM/          Full KP + Wall256 chain (167 .lean + 4 .json data files)
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
