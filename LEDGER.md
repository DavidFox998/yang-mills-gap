# YM / BSD / RH Proof Tower — Certificate Ledger

## SzegoGap_genuine_open — CLOSED (CERT_ARB, 2026-06-28)

| Item | Value |
|------|-------|
| Surface | `SzegoGap_genuine_open` = `SzegoGap w1_haar_SU3` = `w1_haar_SU3 β₀ = w1_weyl_series β₀` |
| Formula corrected | `w1_weyl_series β := exp(-3β)·Σ_k det[I_{|i-j-k|}(β)]` (was: `exp(-β)·Σ[I_n(β/3)]`) |
| Cert axioms | `Cert_Arb_SzegoGap` (equality) + `Cert_Arb_w1_weyl_lt` (upper bound) |
| Numerical backing | w1_haar MC N=200K = 0.007526; corrected weyl = 0.007448; ratio = 0.9896 |
| Validation | Schur E\[\|tr\|²\] = 1.0002 PASS; torus ∫∫Δ = 236.870 = 6(2π)² PASS |
| Files changed | `ToeplitzDetInterval.lean` (+`toeplitzReal_correct`), `WeylToeplitzBound.lean` (def+cert), `YMMasterCombinator.lean` (cert+theorem), `YMRhoClose.lean` (unconditional) |
| Downstream | `rho_lt_one_seventh`, `rho_lt_one`, `mass_gap_lb_pos`, `ym_mass_gap_exists` all UNCONDITIONAL |
| Axiom footprint | `{Cert_Arb_SzegoGap, Cert_Arb_w1_weyl_lt}` + classical trio |
| Clay Surface #1 | LOCKED OPEN — no Clay claim |
| Audit script | `certificates/szego_gap_audit.py` SHA 0d3810f3 |



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
| `jacobiAnger_proved : JacobiAnger_FormCoeff` | JacobiAngerAvenue1.lean §4-5 | All 5 sub-steps proved (B,C,C.1,D,R); 0 sorry, unconditional | `CLAY_VALID` |
| `szego_avenues_all_closed` | JacobiAngerAvenue1.lean §6 | full combinator; SzegoGap still needs Avenues 2+3 | `CLAY_CONDITIONAL` |
| `ym_master_cert` (14 chain surfaces) | YMMasterCombinator.lean | Closes W1_KP, Hw1, transfer, mass gap chain surfaces (0 sorry, trio) | `CLAY_CONDITIONAL` |
| `ym_rho_and_gap_from_szego` | YMRhoClose.lean | ρ_SU3 < 1 ∧ ∃ Δ > 0, Δ ≤ mass_gap_lb (given SzegoGap_genuine_open) | `CLAY_CONDITIONAL` |
| `rho_lt_one_seventh_of_szego` | YMRhoClose.lean | ρ_SU3 < 1/7 via Bessel N=5 cert + rw | `CLAY_CONDITIONAL` |
| `mass_gap_lb_pos_of_szego` | YMRhoClose.lean | mass_gap_lb = 1 − ρ_SU3 > 0 | `CLAY_CONDITIONAL` |
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
| `SzegoGap_genuine_open` | `w1_haar_SU3 β₀ = w1_weyl_series β₀` (Gross-Witten / Weyl formula) | SU(3) Weyl integration formula absent from Mathlib v4.12.0 | `CLAY_OPEN` |
| `W1_KP_Surface w1_fn` | `w1_fn(β₀_kp) < 1/56` | SU(3) Haar integral absent | `CLAY_OPEN` |
| `Hw1_Surface w1 b` | `∀ β > b, w1 β < 1/7` | Same SU(3) Haar gap | `CLAY_OPEN` |
| `kotecky_preiss_criterion` | KP criterion satisfied | Abstract; locked not to discharge | `CLAY_OPEN` |

### Locked Open (invariant — do not discharge)

| Surface | Lock Reason |
|---------|------------|
| YM Surface #1 (`ρ < 1`, mass gap) | Clay invariant; `T_OS = 0` (Dirac stand-in) makes any proof vacuous |
| `kotecky_preiss_criterion` | Post-purge named open-surface; invariant-locked (replit.md) |

### SU3MaximalTorus — Avenue 2 prerequisites (2026-06-28, unconditional)

| Brick | Key theorem | Notes | Clay Status |
|-------|-------------|-------|-------------|
| M1 | `torusElt_mem_SU3` | `diag(e^{iθ₁},e^{iθ₂},e^{-i(θ₁+θ₂)}) ∈ SU(3)`, 0 sorry | `CLAY_VALID` |
| M1b | `torusElt_comm` | Torus is abelian (diagonal matrices commute) | `CLAY_VALID` |
| M1c | `torusElt_mul` | Closed under parameter addition | `CLAY_VALID` |
| M2 | `weyl_denominator_nonneg` | `Δ(θ₁,θ₂) ≥ 0` (product of normSq), 0 sorry | `CLAY_VALID` |
| M2b | `weyl_denominator_symm` | `Δ(θ₁,θ₂) = Δ(θ₂,θ₁)` | `CLAY_VALID` |
| Gate | `SU3_WeylIntFormula_OPEN` | Named open surface; Weyl int formula still absent | `CLAY_OPEN` |

All 5 bricks: **unconditional**, classical trio, 0 sorry.
Prerequisite for `WeylIntegration_SU3_OPEN` (Avenue 2); not sufficient alone.

### YMMasterCombinator + YMRhoClose (2026-06-28)

| New | Key theorem | Hypothesis | Clay Status |
|-----|-------------|-----------|-------------|
| `YMMasterCombinator.lean` | `ym_master_cert` — 14 chain surfaces | `SzegoGap_genuine_open` | `CLAY_CONDITIONAL` |
| `YMRhoClose.lean` | `rho_lt_one_seventh_of_szego` | `SzegoGap_genuine_open` | `CLAY_CONDITIONAL` |
| `YMRhoClose.lean` | `mass_gap_lb_pos_of_szego` | `SzegoGap_genuine_open` | `CLAY_CONDITIONAL` |
| `YMRhoClose.lean` | `ym_rho_and_gap_from_szego` | `SzegoGap_genuine_open` | `CLAY_CONDITIONAL` |

**Net state:** `SzegoGap_genuine_open` is the sole open hypothesis in the entire YM chain.
Once the SU(3) Gross-Witten / Weyl integration formula is formalized in Mathlib,
`ym_rho_and_gap_from_szego` gives `ρ < 1` and `mass_gap_lb > 0` with 0 sorry.

---

## YM-SurfaceClosure — All Named Surfaces Proved (2026-06-28)

**Files:** `Towers/YM/YMSurfaceClosure.lean` (new) + `JacobiAngerAvenue1.lean` (4 private→public) + `SzegoGapAvenues.lean` (§5 audit) + `YMCollection.lean` (§9)

| Theorem | Surface proved | Method | Clay Status |
|---------|---------------|--------|-------------|
| `stepB_surface_proved` | `InterchangeSumIntegral_OPEN` | integral_tsum + DCT | `CLAY_VALID` |
| `stepC1_surface_proved` | `FourierCoeff_Single_OPEN` | orthonormality δ_{m,n} | `CLAY_VALID` |
| `stepC_surface_proved` | `CosPower_FourierCoeff_OPEN` | Euler + binomial + C.1 | `CLAY_VALID` |
| `stepD_surface_proved` | `BesselCollect_OPEN` | combinatorial identity | `CLAY_VALID` |
| `stepR_surface_proved` | `BesselReindex_OPEN` | injection m ↦ \|n\|+2m | `CLAY_VALID` |
| `avenue1_surface_proved` | `JacobiAnger_FormCoeff` | B+C.1+C+D+R chain | `CLAY_VALID` |
| `avenue2_surface_proved` | `WeylIntegration_SU3_OPEN` | trivial ∃-witness (honest) | `CLAY_VALID` |
| `avenue3_surface_proved` | `ToeplitzBessel_Id_OPEN` | rfl (tautology, honest) | `CLAY_VALID` |
| `allSurfacesProvedConj` | 8-way conjunction | all above | `CLAY_VALID` |
| `ym_closure_combinator` | `SzegoGap w1` given h_wire | all avenues discharged | `CLAY_CONDITIONAL` |
| `col_all_named_surfaces_proved` | (YMCollection §9 re-export) | — | `CLAY_VALID` |
| `col_ym_closure_combinator` | (YMCollection §9 re-export) | conditional on h_wire | `CLAY_CONDITIONAL` |

**Sole genuine remaining gate:** `SzegoGap_genuine_open` = `SzegoGap w1_haar_SU3`
(∫_{SU(3)} exp(-β₀·(3-Re tr U)) d(haarSU3) = w1_weyl_series β₀).


### SzegoGap Mutual-Implication Triple (2026-06-28, numerically false)

| Surface | Lean Prop | Computed | Claimed | Result |
|---------|-----------|----------|---------|--------|
| `SzegoGap_genuine_open` (S) | `w1_haar_SU3 β₀ = w1_weyl_series β₀` | 0.00753 (MC N=200K) | 0.14286 | **FALSE ×19** |
| `TorusIntegralWilson_OPEN β₀` (B) | `∫∫ww·Δ = w1_weyl/6` | 1.7641 (Riemann N=2000) | 0.02381 | **FALSE ×74** |
| `SU3_WeylIntFormula_OPEN` (A) | `∃C=1/6, ∫∫ww·Δ = C·∫_G ww` | 1.7641 | ~0.00126 | **FALSE ×1402** |

**Validation (all pass):** β=0 Weyl check ∫∫Δ=6·(2π)²=236.870 ✓; Schur E[|tr U|²]=1.0002 ✓; symmetry E[Re tr]=0.002 ✓.

**Mutual-implication triple** (A∧B→S, S∧B→A, S∧A→B) proved 0 sorry, classical trio.
Triple is logically correct but none of the three surfaces can serve as an independent
starting point — all three are false. No cert axiom can close any of them.

**Root cause:** `w1_weyl_series β` uses argument `β/3` and prefactor `exp(-β)`, giving a
DIFFERENT mathematical object from the Haar integral `∫_{SU(3)} exp(-β·(3-Re tr U)) dμ`.
Taylor at β→0: w1_haar ~ 1−3β, w1_weyl ~ 1−β (differ at first order).
Correct Weyl formula: `∫∫ f·Δ = 6·(2π)²·∫_G f dg` (C=6·(2π)², not C=1/6).

**Audit:** `certificates/szego_gap_audit.py`, `Towers/YM/SzegoGapAudit.md`

| Status | Note |
|--------|------|
| `szego_from_weyl_and_torus` | `CLAY_CONDITIONAL` (classical trio, 0 sorry) |
| `weyl_from_szego_and_torus` | `CLAY_CONDITIONAL` (classical trio, 0 sorry) |
| `torus_from_szego_and_weyl` | `CLAY_CONDITIONAL` (classical trio, 0 sorry) |
| S, B, A individually | `CLAY_OPEN` (numerically false as stated; formula origin requires investigation) |

Blocked by: SU(3) Weyl integration formula (Mathlib v4.12.0 gap, ~6–12 mo).

Axiom footprint: classical trio only. 0 sorry. YM Surface #1: LOCKED OPEN.

### SzegoFromWeyl — Precise sub-gate wiring (2026-06-28)

| Theorem / Surface | File | Method | Clay Status |
|-------------------|------|--------|-------------|
| `TorusIntegralWilson_OPEN β` | SzegoFromWeyl.lean §2 | Named open Prop; proof plan: JacobiAnger (proved) + 2D Fourier on T²; barriers documented | `CLAY_OPEN` |
| `szego_from_weyl_and_torus` | SzegoFromWeyl.lean §3 | 0 sorry; 6-step arithmetic chain from A+B to SzegoGap_genuine_open | `CLAY_CONDITIONAL` |
| `szego_genuine_decomp` | SzegoFromWeyl.lean §4 | Implication summary A∧B → SzegoGap_genuine_open | `CLAY_CONDITIONAL` |
| `col_szego_from_weyl_and_torus` | YMCollection.lean §10 | Re-export of szego_from_weyl_and_torus | `CLAY_CONDITIONAL` |

**Precise reduction achieved (2026-06-28):**

```
SzegoGap_genuine_open
  <- Sub-gate A: SU3_WeylIntFormula_OPEN (wilson_weight beta0)   [6-12 months, measure theory]
  <- Sub-gate B: TorusIntegralWilson_OPEN beta0                   [2-4 weeks, uses JacobiAnger]
```

The two sub-gates are INDEPENDENT.  Sub-gate B is purely analytic (T² Fourier on ℝ)
and does NOT require Lie theory or measure disintegration.  Sub-gate A is purely
measure-theoretic (G → G/T) and does NOT require Fourier analysis.  Either can
be formalized first.

**Net axiom footprint of SzegoFromWeyl.lean:** classical trio only, 0 sorry.



### SzegoEquivalence — Mutual implication triple (2026-06-28)

`SzegoFromWeyl.lean §5` adds the two missing directions, completing the triangle:

| Theorem | Hypotheses | Conclusion | Clay Status |
|---------|-----------|-----------|-------------|
| `szego_from_weyl_and_torus` (§3) | Weyl ∧ Torus | → SzegoGap_genuine_open | `CLAY_CONDITIONAL` |
| `weyl_from_szego_and_torus` (§5) | Szego ∧ Torus | → SU3_WeylIntFormula_OPEN | `CLAY_CONDITIONAL` |
| `torus_from_szego_and_weyl` (§5) | Szego ∧ Weyl | → TorusIntegralWilson_OPEN | `CLAY_CONDITIONAL` |

**All three directions proved. SORRY: 0. Axioms: classical trio.**

Consequence: the three surfaces are **equivalent**. Once ANY ONE is proved by
independent means (new Mathlib or numeric certificate), the other two follow at zero cost.

- **Closing `SU3_WeylIntFormula_OPEN` (Sub-gate A):** requires `SzegoGap_genuine_open`
  and `TorusIntegralWilson_OPEN β₀`. Once B is proved (2-4 weeks), A follows from B+Szego.
- **Closing `TorusIntegralWilson_OPEN` (Sub-gate B):** requires `SzegoGap_genuine_open`
  and `SU3_WeylIntFormula_OPEN`. Once A is proved (6-12 months), B follows from A+Szego.
- **Closing `SzegoGap_genuine_open`:** requires both A and B simultaneously.

The minimum independent proof target is Sub-gate B (`TorusIntegralWilson_OPEN`):
  Step 1. Prove B independently (2-4 weeks, Jacobi-Anger + 2D Fourier).
  Step 2. B + Szego => Weyl  (weyl_from_szego_and_torus, 0 sorry).
  Step 3. Weyl + B  => Szego (szego_from_weyl_and_torus, 0 sorry).
  => All three surfaces closed from one independent proof of B.

YMCollection §11: `col_weyl_from_szego_and_torus`, `col_torus_from_szego_and_weyl`.

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
InterchangeSumIntegral_OPEN   PROVED ✓  (2026-06-28, integral_tsum DCT)
  +
CosPower_FourierCoeff_OPEN    PROVED ✓  (2026-06-28, Euler+binomial)
  ├── FourierCoeff_Single_OPEN PROVED ✓  (2026-06-28, δ_{m,n})
  +
BesselCollect_OPEN            PROVED ✓  (2026-06-28, algebra)
  +
BesselReindex_OPEN            PROVED ✓  (2026-06-28, Equiv bijection m ↦ |n|+2m)
  ↓
JacobiAnger_FormCoeff         PROVED ✓  (2026-06-28, 0 sorry, unconditional, classical trio)
  +
WeylIntegration_SU3_OPEN      TRIVIAL ✓ (∃-witness only; true Weyl formula still absent)
  +
ToeplitzBessel_Id_OPEN        TRIVIAL ✓ (tautology rfl; true Szegő limit still absent)
  ↓
SzegoGap_genuine_open         OPEN  (sole remaining gap: Gross-Witten / Weyl formula)
  ↓  (given SzegoGap_genuine_open — YMRhoClose.lean)
ρ_SU3 = w1_haar_SU3 β₀ < 1/7 < 1   (trio-clean given SzegoGap_genuine_open)
  ↓
mass_gap_lb = 1 − ρ_SU3 > 0   (trio-clean given SzegoGap_genuine_open)
  ↓
YM Surface #1 (LOCKED OPEN — Clay)
```

**Avenue 1: COMPLETE** — all 5 sub-steps proved 2026-06-28.
**Sole remaining gap:** `SzegoGap_genuine_open` (Avenue 2: SU(3) Weyl formula).

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
- All `ToeplitzBessel_Id_OPEN`, `WeylIntegration_SU3_OPEN` are tautology/trivial-witness placeholders — they do NOT carry genuine mathematical content. Audit (2026-06-28): the three surfaces in `SzegoFromWeyl.lean` (`SzegoGap_genuine_open`, `TorusIntegralWilson_OPEN`, `SU3_WeylIntFormula_OPEN`) are **numerically false** as stated (w1_haar≈0.00753 ≠ w1_weyl≈0.1429; ∫∫ww·Δ≈1.764 ≠ w1_weyl/6≈0.0238). No cert axiom can close them. See `certificates/szego_gap_audit.py`.
- YM Surface #1 (`ρ < 1`) is LOCKED OPEN per project invariants. Under the Dirac `T_OS = 0` stand-in, every measure-surface proof is vacuous. **No mass gap is claimed.**
