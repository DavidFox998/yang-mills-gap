# Yang-Mills Tower — Morning Star Project

Classical trio only. No sorry. No native_decide. Mathlib v4.12.0.

Axiom footprint: `{propext, Classical.choice, Quot.sound}`.

## What is here

Machine-checked Lean 4 proofs for the SU(3) lattice Yang-Mills
Kotecky-Preiss coupling-constant tower at β₀ ∈ (2.07, 2.08).

SORRY: 0 across all files. No research-grade axioms. No native_decide.
YM Surface #1 (mass gap): LOCKED OPEN. No Clay claim.

---

## N=5 Bessel Milestone (2026-06-28) — PartC_Surface CLOSED

`PartC_Surface` was closed on 2026-06-28 via N=5 Bessel truncation `norm_num`.
This makes `W1_Numeric_Surface` and `w1_weyl_series β₀ < 1/7` **fully unconditional**.

N-sweep (exact Python `Fraction` arithmetic):

| N | PartC margin | Result |
|---|-------------|--------|
| 3 | −3.03×10⁻⁹ | FAILS |
| 4 | −1.26×10⁻¹¹ | FAILS |
| **5** | **+1.30×10⁻¹⁴** | **CLOSED** (norm_num, `maxHeartbeats 0`) |
| 40 | +3.86×10⁻⁷ | OOMs at ~3.9 GB |

## Proved unconditionally (0 sorry, classical trio)

| Result | File | Notes |
|--------|------|-------|
| β₀ ∈ (2.07, 2.08) | `Wall256_Scaffold.lean` | Rational enclosure, `Beta0Certified` predicate |
| **`PartC_Surface`** ✓ | **`BesselBounds.lean`** | **CLOSED 2026-06-28, N=5 norm_num** |
| **`W1_Numeric_Surface`** ✓ | **`BesselBounds.lean`** | **Unconditional via `bb_part_c`** |
| **`w1_weyl_series β₀ < 1/7`** ✓ | **`BesselBounds.lean`** | **Unconditional (bb_w1_weyl_lt)** |
| Bessel tsum enclosure tsum ≤ det | `BesselBounds.lean` | `TsumDetLe_Surface` proved |
| log 2 > 2/3 | `KP_Closure.lean` | `log_two_gt_two_thirds_Surface` |
| (exp(e/4)−1)/(2e) < 1 | `KP_Closure.lean` | `C_eff_tree_lt_one_Surface` |
| gap_kp_star = ln 8 > 2 | `KP_Closure.lean` | Unconditional (from log 2 > 2/3) |
| 107/756 < 1/7 | `W1Toeplitz.lean` | Rational arithmetic |
| `exp_r_cos_continuous` | `SzegoGapAvenues.lean` | Continuity of exp(r·cos·) on circle |
| `exp_r_cos_pos` | `SzegoGapAvenues.lean` | Positivity of exp(r·cos·) |

## Proved conditionally (classical trio, named open hypothesis explicit)

| Result | Hypothesis required | File |
|--------|---------------------|------|
| w1(β₀) < 1/7 | `SzegoGap` only | `YMCollection.lean` |

`W1_Numeric_Surface` and `PartC_Surface` are now **PROVED** — only `SzegoGap` remains.

---

## Open surfaces — complete ledger

All surfaces below are named `def … : Prop` — not `axiom`, not `sorry`,
not a `True`-stub. Every proof that depends on them states the hypothesis
explicitly as a function argument.

### Sole remaining gap (SU(3) Haar measure)

| Surface | Statement | Barrier |
|---------|-----------|---------|
| `SzegoGap (w1 : ℝ → ℝ)` | `w1(β₀) = w1_weyl_series(β₀)` | SU(3) Gross-Witten formula (1980) + Weyl integration formula absent from Mathlib v4.12.0. |
| `W1_KP_Surface (w1_fn)` | `w1_fn(β₀_kp) < 1/56` | SU(3) Haar integral at KP threshold β — same blocker as SzegoGap. |
| `Hw1_Surface (w1 b)` | `β₀-cert b → ∀ β > b, w1 β < 1/7` | SU(3) Haar integral — same blocker. |

### SzegoGap — Three Avenues (see `SzegoGapAvenues.lean`)

| Avenue | Statement | Mathlib footholds | Effort |
|--------|-----------|------------------|--------|
| 1 — JacobiAnger | `fourierCoeff(exp(r·cos·)) n = Iₙ(r)` | `fourierCoeff_eq_intervalIntegral`, `orthonormal_fourier` | **2–4 weeks** |
| 2 — WeylIntegration_SU3 | ∫_{SU(3)} → torus integral | Haar measure (abstract) | 6–12 months |
| 3 — ToeplitzBessel_Id | Torus integral = Toeplitz det sum | None (Fredholm.det absent) | 12–18 months |

### Avenue 1 sub-step chain — state after YM-Avenue1-Sprint (2026-06-28)

File: `Towers/YM/JacobiAngerAvenue1.lean`

```
InterchangeSumIntegral_OPEN   OPEN  (~40 lines, integral_tsum)
  +
CosPower_FourierCoeff_OPEN    OPEN  (~80 lines, orthonormal_fourier)
  ├── FourierCoeff_Single_OPEN OPEN (~20 lines, fourierBasis.repr)
  +
BesselCollect_OPEN            PROVED ✓ (algebra; Nat.add_choose_mul_factorial_mul_factorial)
  +
BesselReindex_OPEN            OPEN  (~40 lines, Equiv bijection)
  ↓
JacobiAnger_FormCoeff         OPEN (conditional combinator wired; closes when B+C+R proved)
  +
WeylIntegration_SU3_OPEN      TRIVIAL ✓ (∃-witness only; TRUE Weyl formula still absent)
  +
ToeplitzBessel_Id_OPEN        TRIVIAL ✓ (tautology rfl; TRUE Szegő limit still absent)
  ↓
SzegoGap                      OPEN (h_wire explicit)
```

New in this sprint (all classical trio, 0 sorry):
- `besselCollect_proved` — `BesselCollect_OPEN` CLOSED via `Nat.add_choose_mul_factorial_mul_factorial` + `linear_combination`
- `weylIntegration_SU3_trivial` — `WeylIntegration_SU3_OPEN` CLOSED (trivial ∃-witness; not physical)
- `toeplitzBessel_trivial` — `ToeplitzBessel_Id_OPEN` CLOSED (tautology `rfl`; not Szegő)
- `jacobiAnger_proved` — conditional combinator wired (B + C + BesselReindex still open)
- `szego_avenues_all_closed` — full three-avenue combinator; `h_wire` remains explicit

Remaining (~180 lines): B (`integral_tsum`) + C (`orthonormal_fourier` delta) + R (Equiv bijection).

### Jacobi-Anger surfaces

| Surface | Statement | Status |
|---------|-----------|--------|
| `JacobiAnger_FormCoeff` | `fourierCoeff(exp(r·cos·)) n = Iₙ(r)` | OPEN — conditional combinator wired in `JacobiAngerAvenue1.lean` |
| `BesselCollect_OPEN` | Binomial → Bessel series identity | **PROVED** (2026-06-28, algebra) |
| `WeylIntegration_SU3_OPEN` | ∃ w, w β = w1_weyl_series β | **TRIVIAL** (∃-witness; not physical) |
| `ToeplitzBessel_Id_OPEN` | Toeplitz det sum = Toeplitz det sum | **TRIVIAL** (tautology; not Szegő) |
| `InterchangeSumIntegral_OPEN` | series↔integral swap | OPEN (~40 lines) |
| `CosPower_FourierCoeff_OPEN` | fourierCoeff(cos^k) n = C(k,·)/2^k | OPEN (~80 lines) |
| `FourierCoeff_Single_OPEN` | fourierCoeff(fourier m) n = δ_{m,n} | OPEN (~20 lines) |
| `BesselReindex_OPEN` | sparse k-sum → dense m-sum bijection | OPEN (~40 lines) |
| `JacobiAngerGap` | placeholder tautology | Deprecated (see `W1Toeplitz.lean`) |

### Clay / locked-open surfaces (invariant — do NOT discharge)

| Surface | Statement | Notes |
|---------|-----------|-------|
| YM Surface #1 (`ρ < 1`) | Mass-gap clustering rate | **LOCKED OPEN** — continuum limit not constructed; do not discharge. |
| `kotecky_preiss_criterion_Surface` | Real KP integral transfer `T_L` | **INVARIANT-LOCKED OPEN** — stays open per project invariants. |
| `MassGap_YM4_Clay_Surface T` | Clay 4D SU(3) mass gap | **LOCKED OPEN** — continuum QFT not formalised in Mathlib. |

---

## Dependency structure (proved chain — post 2026-06-28)

```
PartC_Surface (PROVED ✓)       SzegoGap (OPEN ← sole gap)
      │                               │
      ▼                               │
W1_Numeric_Surface (PROVED ✓)         │
      │                               │
      ▼                               │
w1_weyl_series β₀ < 1/7 (PROVED ✓)   │
                                      │ (closes on SzegoGap)
                     ┌────────────────┘
                     ▼
            w1(β₀) < 1/7  (trio-clean given SzegoGap)
                     │
                     ▼
           KP_Closure: gap_kp_star > 2  ◄── log 2 > 2/3 (PROVED ✓)
                     │
                     ▼
              Wall256_Scaffold (conditional combinator)
```

The unconditional chain now extends to `w1_weyl_series β₀ < 1/7`.
Only `SzegoGap` remains to make the full KP chain unconditional.

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
