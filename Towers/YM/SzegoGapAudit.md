# SzegoGap Numerical Audit (2026-06-28)

## Status

**All three surfaces in `SzegoFromWeyl.lean` §3-§5 are NUMERICALLY FALSE.**

No cert axiom can close them. Opera Numerorum rule: no fabricated values.

## The Three Surfaces

| Surface | Lean Prop | Computed | Claimed | False by |
|---------|-----------|----------|---------|----------|
| `SzegoGap_genuine_open` (S) | `w1_haar_SU3 beta0 = w1_weyl_series beta0` | 0.00753 | 0.14286 | ~19x |
| `TorusIntegralWilson_OPEN beta0` (B) | `int_T ww*Delta = w1_weyl/6` | 1.7641 | 0.02381 | ~74x |
| `SU3_WeylIntFormula_OPEN` (A) | `exists C=1/6, int_T = C * int_G` | 1.7641 | 0.00126 | ~1402x |

## Validation Checks (all pass)

- **Weyl formula at beta=0:** `int_T Delta d theta1 d theta2 = 6*(2*pi)^2 = 236.870`
  Riemann N=2000: 236.870 MATCH.
- **Schur orthogonality:** `E[|tr U|^2] = 1` for U in SU(3) Haar.
  Monte Carlo N=200K: E[|tr|^2] = 1.0002. PASS.
- **Symmetry:** `E[Re tr U] = 0`.
  Monte Carlo N=200K: E[Re tr] = 0.002. PASS.
- **Weyl formula at beta0:** `int_T ww*Delta / (6*(2*pi)^2) = w1_haar`
  1.7641 / 236.870 = 0.00745, MC gives 0.00753. AGREE (finite-N Riemann error).

## Correct Weyl Formula

The standard Weyl integration formula for SU(3) is:

```
int_{SU(3)} f d(haar) = (1 / (6 * (2*pi)^2)) * int_0^{2pi} int_0^{2pi} f(torusElt t1 t2) * Delta d t1 d t2
```

So `C = 1 / (6 * (2*pi)^2)`, NOT `C = 1/6`. The proposition
`SU3_WeylIntFormula_OPEN` claims `C = 1/6` which is off by `(2*pi)^2 = 39.478`.

## Root Cause: w1_weyl_series is a Different Object

```
w1_weyl_series beta = exp(-beta) * sum_{k in Z} det[I_{|i-j-k|}(beta/3)]_{3x3}
```

This formula does NOT equal `int_{SU(3)} exp(-beta*(3-Re tr U)) d(haar)`.

They agree at beta=0 (both equal 1) but diverge immediately for beta > 0.

Taylor expansion at beta -> 0:
- `w1_haar ~ 1 - 3*beta + O(beta^2)` (coefficient 3 = N for SU(N))
- `w1_weyl ~ 1 - beta + O(beta^2)` (coefficient 1, not 3)

The Bessel argument `beta/3` in the Toeplitz formula suggests a rescaled model.
The formula's mathematical origin and intended meaning require investigation.

## Mutual-Implication Triple

The triple `A /\ B -> S`, `S /\ B -> A`, `S /\ A -> B` is proved (0 sorry, classical trio)
in `SzegoFromWeyl.lean §5`. This is logically correct but does not help:
since all three are false, no single one can serve as an independent starting point.

Once the CORRECT Gross-Witten / Weyl formula for `w1_haar_SU3` is identified,
the triple will close all three simultaneously from one proved surface.

## Next Steps

1. Understand the origin of the `w1_weyl_series` formula.
   Does it compute a DIFFERENT physical quantity (e.g., rescaled beta, different weight)?
2. If `w1_weyl_series` was meant to equal `w1_haar`, find the derivation error.
3. If `w1_weyl_series` is correct for a different model, redefine `SzegoGap_genuine_open`
   with the correct equality (using the numerically verified value ~0.00753).

## Files

- Audit script: `certificates/szego_gap_audit.py`
- Lean surfaces: `Towers/YM/SzegoFromWeyl.lean` (S3-S5, mutual implication triple)
- Avenues: `Towers/YM/SzegoGapAvenues.lean` (Avenue 2+3 stubs)
- w1_weyl def: `Towers/YM/WeylToeplitzBound.lean`

YM Surface #1 (Clay mass gap): LOCKED OPEN. No Clay claim.
