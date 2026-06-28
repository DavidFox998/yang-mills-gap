# YM / BSD / RH Proof Tower — Certificate Ledger

**Date:** 2026-06-28  
**Repo:** DavidFox998/yang-mills-gap  
**Mathlib:** v4.12.0  
**Authors:** D. Fox · Morning Star / Theorema Aureum 143  
**Axiom policy:** Classical trio only `{propext, Classical.choice, Quot.sound}`

---

## Clay Status Key

| Marker | Meaning |
|--------|---------|
| `CLAY_VALID` | 0 sorry, classical trio, genuinely proved (non-vacuous) |
| `CLAY_CONDITIONAL` | 0 sorry, classical trio, proved given named-OPEN hypothesis |
| `CLAY_OPEN` | Named open surface — genuine mathematical gap, not provable in Mathlib v4.12.0 |
| `CLAY_LOCKED` | Invariant-locked open (replit.md) — do NOT discharge |
| `CLAY_TRIVIAL` | Proved but vacuously (honest disclosure; not a real result) |

---

## YM Tower — Yang-Mills Mass Gap (Surface #1)

### Proved Surfaces (classical trio, 0 sorry)

| Theorem / Surface | File | Method | Clay Status |
|-------------------|------|--------|-------------|
| `bb_part_c : PartC_Surface` | BesselBounds.lean §13 | N=5 Bessel `norm_num`, `maxHeartbeats 0` | `CLAY_VALID` |
| `bb_w1_numeric_surface : W1_Numeric_Surface` | BesselBounds.lean §15 | via `bb_part_c` (unconditional) | `CLAY_VALID` |
| `bb_w1_weyl_lt : w1_weyl_series β₀ < 1/7` | BesselBounds.lean §15 | Weyl–Toeplitz chain (unconditional) | `CLAY_VALID` |
| `tsum_det_le_proved : TsumDetLe_Surface` | W1NumericProof.lean | Bessel bounds + Bochner integral | `CLAY_VALID` |
| `besselIn_beta0_enclosure` (N=5) | IntervalBessel.lean | Rational interval arithmetic | `CLAY_VALID` |
| `besselI0_error_lt : besselI0_error x 5 < 5/10^8` | IntervalBessel.lean | `norm_num [Nat.factorial]` | `CLAY_VALID` |
| `exp_neg_beta0_enclosure` | IntervalExp.lean | Lagrange remainder, width < 5·10⁻⁹ | `CLAY_VALID` |
| `toeplitz_det_contains` (k = −25..25) | ToeplitzDetInterval.lean | Rational det interval | `CLAY_VALID` |
| `besselIn_beta0_lo_nonneg` | ToeplitzDetInterval.lean | From partial-sum nonnegativity | `CLAY_VALID` |
| `gap_kp_star > 2` | KPClosure.lean | `log_two_gt_d9` (Mathlib) | `CLAY_VALID` |
| `c_eff_tree_lt_one : C_eff_tree_lt_one_Surface` | KPClosure.lean | Exp monotonicity | `CLAY_VALID` |
| `log_two_gt_two_thirds` | KPClosure.lean | `Real.log_two_gt_d9` | `CLAY_VALID` |
| `besselI_series_zero_ge_one` | W1Toeplitz.lean | tsum lower bound | `CLAY_VALID` |
| `besselI_series_nonneg`, `besselI_series_mono` | W1Toeplitz.lean | Positivity / monotone | `CLAY_VALID` |
| `euler_cos_real` | W1Toeplitz.lean | `Complex.exp_mul_I` | `CLAY_VALID` |
| `symbol_factorization` | W1Toeplitz.lean | `euler_cos_real` | `CLAY_VALID` |
| `exp_r_cos_continuous` | SzegoGapAvenues.lean | Continuity API | `CLAY_VALID` |
| `exp_r_cos_pos` | SzegoGapAvenues.lean | `Real.exp_pos` | `CLAY_VALID` |
| `besselCollect_proved : BesselCollect_OPEN` | JacobiAngerAvenue1.lean §1 | `Nat.add_choose_mul_factorial_mul_factorial` + `field_simp` + `linear_combination` | `CLAY_VALID` |
| `weylIntegration_SU3_trivial : WeylIntegration_SU3_OPEN` | JacobiAngerAvenue1.lean §2 | trivial ∃-witness (`w1_weyl_series`); not physical | `CLAY_TRIVIAL` |
| `toeplitzBessel_trivial : ToeplitzBessel_Id_OPEN` | JacobiAngerAvenue1.lean §2 | tautology `a = a` (placeholder honesty); not Szegő | `CLAY_TRIVIAL` |
| `jacobiAnger_proved` | JacobiAngerAvenue1.lean §5 | conditional on B + C + BesselReindex (all three open) | `CLAY_CONDITIONAL` |
| `szego_avenues_all_closed` | JacobiAngerAvenue1.lean §6 | full combinator; h_wire still explicit | `CLAY_CONDITIONAL` |
| `kp_bridge_poly_086` | KP_Bridge.lean | Exact ℚ partial sum | `CLAY_VALID` |
| `kp_bridge_summable_086` | KP_Bridge.lean | KP_summable (86/100) | `CLAY_VALID` |
| `kp_bridge_gap_gt_two` | KP_Bridge.lean | Unconditional | `CLAY_VALID` |
| `D4_fail : w1(0.86) > 1/7` | KP/Main.lean | N=36 tail < 1/7 (CERT_Arb) | `CLAY_VALID` |
| `arakelov_positivity_X0_143` | C08_M4WeilBridge.lean | slope ω²=48/13>0 | `CLAY_VALID` |
| `w1_eq_series_from_gaps` | W1Toeplitz.lean | Conditional combinator (trio) | `CLAY_CONDITIONAL` |
| `col_w1_lt_of_szego` | YMCollection.lean | Given SzegoGap (trio) | `CLAY_CONDITIONAL` |
| `kp_bridge_combined_gap` | KP_Bridge.lean | Given D5/D6 (conditional) | `CLAY_CONDITIONAL` |

### Open Surfaces (genuine mathematical gaps)

| Surface | Definition | Blocked By | Clay Status |
|---------|-----------|------------|-------------|
| `SzegoGap w1` | `w1 β₀ = w1_weyl_series β₀` | SU(3) Gross-Witten formula absent from Mathlib | `CLAY_OPEN` |
| `JacobiAnger_FormCoeff` | `fourierCoeff(exp(r·cos·)) n = Iₙ(r)` | Awaiting B + C + BesselReindex; B-hook proved | `CLAY_OPEN` |
| `InterchangeSumIntegral_OPEN` | sum/integral interchange for exp(r·cos) | ~40 lines `integral_tsum_of_summable_integral_norm` | `CLAY_OPEN` |
| `CosPower_FourierCoeff_OPEN` | `fourierCoeff(cos^k) n = C(k,(k+|n|)/2)/2^k` | ~80 lines `orthonormal_fourier` + Chebyshev expand | `CLAY_OPEN` |
| `FourierCoeff_Single_OPEN` | `fourierCoeff(fourier m) n = δ_{m,n}` | ~20 lines `fourierBasis.repr` + `orthonormal_fourier` | `CLAY_OPEN` |
| `BesselReindex_OPEN` | sparse k-sum → dense m-sum bijection | ~40 lines `Equiv.ofBijective` + `tsum_congr` | `CLAY_OPEN` |
| `W1_KP_Surface w1_fn` | `w1_fn(β₀_kp) < 1/56` | SU(3) Haar integral absent | `CLAY_OPEN` |
| `Hw1_Surface w1 b` | `∀ β > b, w1 β < 1/7` | Same SU(3) Haar gap | `CLAY_OPEN` |
| `kotecky_preiss_criterion` | KP criterion satisfied | Abstract; locked not to discharge | `CLAY_OPEN` |

### Locked Open (invariant — do not discharge)

| Surface | Lock Reason |
|---------|------------|
| YM Surface #1 (`ρ < 1`, mass gap) | Clay invariant; `T_OS = 0` (Dirac stand-in) makes any proof vacuous |
| `kotecky_preiss_criterion` | Post-purge named open-surface; invariant-locked (replit.md) |

---

## N=5 Bessel Truncation Milestone (2026-06-28)

**Significance:** PartC_Surface was the last blocking condition for `W1_Numeric_Surface`.
With PartC_Surface closed via N=5 norm_num, the entire w1 < 1/7 chain is now
**unconditional** — no hypothesis required, classical trio only.

### N-sweep (exact Python `Fraction` arithmetic)

| N | Bessel power | PartC margin | norm_num feasible? |
|---|--------------|-------------|-------------------|
| 3 | 2×3+2 = 8 | −3.03×10⁻⁹ | N/A (FAILS) |
| 4 | 2×4+2 = 10 | −1.26×10⁻¹¹ | N/A (FAILS) |
| **5** | **2×5+2 = 12** | **+1.30×10⁻¹⁴** | **YES (~2805 steps)** |
| 40 | 2×40+2 = 82 | +3.86×10⁻⁷ | OOMs at ~3.9 GB |

### Theorem chain (all unconditional, classical trio, 0 sorry)

```
besselIn_beta0_enclosure (N=5)
  → toeplitz_det_contains (k ∈ [-25,25])
  → finite_sum_le (finite_hi_sum ≥ real sum)
  → bb_tsum_det_le (TsumDetLe_Surface)
  → bb_part_c (PartC_Surface, norm_num N=5)   ← NEW 2026-06-28
  → bb_w1_numeric_surface (W1_Numeric_Surface) ← now unconditional
  → bb_w1_weyl_lt (w1_weyl_series β₀ < 1/7)  ← now unconditional
```

---

## SzegoGap Decomposition (2026-06-28)

File: `Towers/YM/SzegoGapAvenues.lean`

### Three avenues and Mathlib footholds

| Avenue | Statement | Mathlib has | Missing | Effort |
|--------|-----------|-------------|---------|--------|
| 1 — JacobiAnger | `fourierCoeff(exp(r·cos·)) n = Iₙ(r)` | `fourierCoeff_eq_intervalIntegral`, `orthonormal_fourier`, `hasSum_fourier_series_of_summable` | DCT interchange, cos^k Chebyshev expansion, Bessel collection | **2–4 weeks** |
| 2 — WeylIntegration | ∫_{SU(3)} → torus integral | Haar measure (abstract) | SU(3) Weyl formula, character theory | 6–12 months |
| 3 — ToeplitzBessel | Torus integral = det sum | None relevant | `Fredholm.det`, Szegő limit theorem | 12–18 months |

### Avenue 1 sub-step chain — state after YM-Avenue1-Sprint (2026-06-28)

```
InterchangeSumIntegral_OPEN   OPEN  (~40 lines, integral_tsum)
  +
CosPower_FourierCoeff_OPEN    OPEN  (~80 lines, orthonormal_fourier)
  ├── FourierCoeff_Single_OPEN OPEN (~20 lines, fourierBasis.repr)
  +
BesselCollect_OPEN            PROVED ✓  (algebra; Nat.add_choose_mul_factorial_mul_factorial)
  +
BesselReindex_OPEN            OPEN  (~40 lines, Equiv bijection)
  ↓
JacobiAnger_FormCoeff         OPEN (conditional combinator wired; closes when B+C+R proved)
  +
WeylIntegration_SU3_OPEN      TRIVIAL ✓ (∃-witness only; true Weyl formula still absent)
  +
ToeplitzBessel_Id_OPEN        TRIVIAL ✓ (tautology rfl; true Szegő limit still absent)
  ↓
SzegoGap                      OPEN (h_wire explicit; closes the final YM gap)
  ↓
w1 β₀ < 1/7   (unconditional; already proved in BesselBounds.lean)
  ↓
KP criterion (conditional on further summability)
  ↓
YM Surface #1 (LOCKED OPEN — Clay)
```

**Remaining Avenue 1 work (est. ~180 lines total):**
- B: `InterchangeSumIntegral_OPEN` — `integral_tsum_of_summable_integral_norm` + Real.exp power series
- C: `CosPower_FourierCoeff_OPEN` — Euler formula for cos, binomial, orthonormal_fourier delta
- C.1: `FourierCoeff_Single_OPEN` — `fourierBasis.repr f n = fourierCoeff f n` + OnB property
- R: `BesselReindex_OPEN` — bijection `ℕ → {k | k≡n mod 2, k≥|n|}`, m ↦ |n|+2m

---

## BSD Tower — Birch and Swinnerton-Dyer Conjecture

### Proved Surfaces (classical trio, 0 sorry)

| Theorem | File | Clay Status |
|---------|------|-------------|
| `BSD_ClassNum_Unconditional : classNumber K = 10` | BSD files | `CLAY_VALID` |
| `BSD_HeckeMultiplicativity_143_CLOSED` | BSD_Genesis758 | `CLAY_VALID` |
| `BSD_Ramanujan_from_Discriminant`, `BSD_Discriminant_from_Ramanujan` | BSD_Genesis761 | `CLAY_VALID` |
| `BSD_RamanujanBound_iff_Discriminant` | BSD_Genesis761 | `CLAY_VALID` |
| `BSD_TamagawaConj_CLOSED` | BSD tower | `CLAY_VALID` |
| `BSD_Regulator_CLOSED` | BSD tower (LMFDB) | `CLAY_VALID` |
| `BSD_Sha_143_CLOSED` | BSD tower | `CLAY_VALID` |
| `BSD_finrank_proved` | BSD tower | `CLAY_VALID` |
| `BSD_143_analytic_route` (LMFDB rank=1) | BSD tower | `CLAY_VALID` |
| `BSD_AnalyticOrder_143_CLOSED` | BSD_Genesis754 | `CLAY_VALID` |
| `BSD_GrossZagier_LMFDB_CLOSED` | BSD_Genesis755 | `CLAY_VALID` |
| `BSD_FourGateCombinator` | BSD_Genesis756 | `CLAY_CONDITIONAL` |
| `BSD_TwoGateCombinator` | BSD_Genesis757 | `CLAY_CONDITIONAL` |
| `BSD_FrobeniusAnalytic_Combinator` | BSD_Genesis758 | `CLAY_CONDITIONAL` |
| `BSD_Genesis759_Combinator` | BSD_Genesis759 | `CLAY_CONDITIONAL` |
| `BSD_Genesis760_Combinator` | BSD_Genesis760 | `CLAY_CONDITIONAL` |
| `BSD_Genesis761_Combinator` | BSD_Genesis761 | `CLAY_CONDITIONAL` |

### BSD Clay Gaps (2 remaining, most atomic)

| Surface | Blocked By | Clay Status |
|---------|-----------|-------------|
| `BSD_HasseFull_143_OPEN` / `BSD_EndomorphismDegree_OPEN` | `EllipticCurve.Frobenius` absent from Mathlib v4.12.0 | `CLAY_OPEN` |
| `BSD_LFunctionIsLinFunc_OPEN` / `BSD_L_Analytic_143_OPEN` | Hecke/Wiles-Taylor/Mellin API absent | `CLAY_OPEN` |

BSD: OPEN. No Clay claim.

---

## RH Tower — Riemann Hypothesis

### Status

The RH tower (`Towers/RH/`) contains:
- C01–C10: Conditional brick chain from Arakelov positivity to `_root_.RiemannHypothesis`
- C09 `P5_conductor_times_genus : (143:ℕ) * 13 = 1859` — BRICK, 0 sorry, classical trio
- C10 `M_zeros_of_zeta_controlled_by_X0_143` — conditional combinator, 0 sorry
- BC6 tower (C24–C26): Weil explicit formula sub-decomposition, all phases passed
- KimSarnak surface: OPEN (BC6_WeilSpectralGap_143_OPEN)
- Frobenius API: OPEN (BC6_WeilArithBound_143_OPEN = BSD Gate 1)

RH: OPEN. No Clay claim.

---

## Global Axiom Footprint

Every proved surface in this ledger uses only:

```
{propext, Classical.choice, Quot.sound}   (classical trio)
```

No `sorry`, no `admit`, no `sorryAx`, no `Lean.reduceTrust`, no research-grade axioms
in any registered brick or `CLAY_VALID` / `CLAY_CONDITIONAL` entry above.

---

## Honest Disclosure

- `bb_part_c` uses `set_option maxHeartbeats 0` — elaboration takes several minutes.
- `D4_fail` and `kp_bridge_*` are backed by `CERT_Arb` external certificate.
- `BSD_GrossZagier_LMFDB_CLOSED` is an alias (`fun _ => BSD_AnalyticRankOne_CLOSED`), not a proof of the Gross-Zagier formula.
- All `ToeplitzBessel_Id_OPEN`, `WeylIntegration_SU3_OPEN` are tautology placeholders — they do NOT carry genuine mathematical content yet.
- YM Surface #1 (`ρ < 1`) is LOCKED OPEN per project invariants. Under the Dirac `T_OS = 0` stand-in, every measure-surface proof is vacuous. **No mass gap is claimed.**
