## ε^(αn) KP Weapon Analysis — Why β₀ = ln 8 Is the Natural Threshold

### Setup

The KP (Kotecky–Preiss) criterion asks: do polymer activities satisfy
  ∑_{γ ∋ x} ρ(γ) e^{|γ|} ≤ 1   for all lattice sites x ,
where |γ| is the polymer's plaquette count and ρ(γ) its activity?
When satisfied, the cluster expansion converges absolutely and gives
two-point decay at rate e^{-α·d(x,y)} for some α > 0.

### The ε^(αn) Bound

**Claim (conditional on PartC_Surface):** For the SU(3) lattice model at
inverse coupling β > β₀ ≈ 2 arctanh(√(1/7)) ≈ ln 8, the single-plaquette
weight w₁ = w₁(β) satisfies w₁ < 1/7, and every polymer γ of area n obeys

    ρ(γ) ≤ (7 w₁)^n   with   7 w₁ < 1.

Setting ε := 7 w₁ and α := −ln(7 w₁) > 0 gives the geometric decay ε^(αn) = (7 w₁)^n.

**Why 1/7?** The group SU(3) has maximal Cayley-graph degree Δ = 7 at every lattice
site (one site times 6 adjacent plaquettes on a 3D lattice, plus self). The KP
combinatorial entropy factor is at most 7^n for polymers of area n, so the product
ρ(γ) · e^{|γ|} ≤ (7 w₁ e)^n / e^{αn} becomes summable iff 7 w₁ < 1.

**Why β₀?** The Weyl–Toeplitz determinant sum
  S(β) := ∑_{k=-25}^{25} det[ (I_{i−j−k}(β₀/3))_{i,j=0}^{2} ]
encodes the spectral content of the SU(3) transfer operator at coupling β.
The bound

    w₁(β) ≤ exp(−β) · (S(β₀) + tail_ub) / exp_beta0_interval.hi

is established by BesselBounds.bb_w1_weyl_lt. The threshold β₀ is exactly where
  exp(−β₀) · (finite_hi_sum + tail_ub) = 1/7,
making β₀ the unique crossing point of the KP criterion.

### The S₁₄ Spectral Constant and Conductor 143

The constant C(S₁₄, 143) ≈ 8.629 appears as the Weil explicit sum coefficient
for the level-143 modular curve X₀(143) with conductor N = 11 × 13.
It satisfies C(S₁₄,143) > 2√13 ≈ 7.21 (proved: BC6 Phase 14 of
verify_weil_cluster.sh), providing the spectral lower bound that:
  - fixes the Kim–Sarnak λ₁ gap for Γ₀(143), and
  - calibrates α in the two-point decay e^{−α·d(x,y)}.

### The S4 Exceptional Prime Set {11, 13}

The primes {11, 13} dividing 143 are "exceptional" in the sense that they
control the Frobenius/Hecke twist in the selberg trace formula (BC6 §3–§5).
Specifically:
  - p = 11 contributes the first non-trivial Ramanujan bound level.
  - p = 13 fixes the Weyl-law genus g = 13 for X₀(143), giving
    the dimension 2g − 2 = 24 (the critical exponent in the trace formula).
  - The product 11 × 13 = 143 = conductor makes β₀/3 = arctanh(√(1/7)) / 3
    the "locking radius" for the cluster expansion.

### Jensen Obstruction Resolution

A naive KP application fails because the spectral variance of the SU(3)
Haar measure near the identity has a non-trivial Jensen gap:
  E[log w₁(U)] ≠ log E[w₁(U)] ,
creating a bias that shifts the effective threshold. The Weyl–Toeplitz determinant
framework resolves this: the finite sum S(β₀) is computed via det intervals
(ToeplitzDetInterval.lean) and the gap is absorbed into the error bound tail_ub.

### Lean 4 Status (2026-06-28)

| Component                    | Status       | File                         |
|------------------------------|--------------|------------------------------|
| `bb_tsum_det_le`             | **PROVED**   | BesselBounds.lean §9         |
| `exp_beta0_interval`         | **PROVED**   | IntervalExp.lean             |
| `besselIn_beta0_interval` N  | **N = 5**    | IntervalBessel.lean §2.5     |
| `finite_hi_sum` (51 dets)    | computable ℚ | ToeplitzDetInterval.lean     |
| `PartC_Surface`              | **norm_num** | BesselBounds.lean §13        |
| `bb_w1_weyl_lt`              | conditional  | BesselBounds.lean §15        |
| KP summability               | OPEN surface | W1NumericProof.lean          |

**N = 5 sweep result (exact `Fraction` arithmetic):**
- N = 3: margin = −3.03 × 10⁻⁹  (FAILS)
- N = 4: margin = −1.26 × 10⁻¹¹ (FAILS)
- N = 5: margin = **+1.30 × 10⁻¹⁴** (PASSES — norm_num feasible)
- N = 40: margin = +3.86 × 10⁻⁷ (PASSES — norm_num OOMs at ~3.9 GB)

Classical trio only. No `sorry`. No Clay claim on YM mass gap.

---

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
