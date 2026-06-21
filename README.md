# Yang-Mills Tower — Morning Star Project

Classical trio only. No sorry. No native_decide. Mathlib v4.12.0.

Axiom footprint: `{propext, Classical.choice, Quot.sound}`.

## What is here

Machine-checked Lean 4 proofs for the SU(3) lattice Yang-Mills
Kotecky-Preiss coupling-constant tower at β₀ ∈ (2.07, 2.08).

### Proved (0 sorry, classical trio)

| Result | File | Status |
|--------|------|--------|
| β₀ ∈ (2.07, 2.08) | `Towers/YM/Wall256_Scaffold.lean` | BRICK |
| Bessel enclosure tsum ≤ det | `Towers/YM/BesselBounds.lean` | BRICK |
| W1 numeric bound w1 ≤ 107/756 | `Towers/YM/BesselBounds.lean` | BRICK |
| 107/756 < 1/7 | `Towers/YM/W1Toeplitz.lean` | BRICK |
| KP gap_kp_star > 2 | `Towers/YM/KP_Closure.lean` | BRICK |
| YM collection entry-point | `Towers/YM/YMCollection.lean` | WIRED |

### Open surfaces (named hypotheses, not `sorry`)

| Surface | Reason open |
|---------|-------------|
| `SzegoGap` — w1(β₀) = w1_weyl_series(β₀) | SU(3) Gross-Witten formula absent from Mathlib v4.12.0 |
| `W1_KP_Surface` | SU(3) Haar integral absent |
| YM Surface #1 (mass gap) | **LOCKED OPEN** — continuum limit not constructed |

## Structure

```
Towers/YM/   — Lean files: full KP chain + Wall256 bridge
KP/          — standalone KP certificate
lakefile.lean      — Mathlib v4.12.0, lean_lib Towers + KP
lean-toolchain     — leanprover/lean4:v4.12.0
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

---

## Clay-rules audit

Run `python3 audit_sorry.py` from the repo root to verify every `.lean` file
is free of real `sorry` proof terms and non-trio `axiom` declarations.
The script strips block comments (`/- … -/`), line comments (`-- …`), and
string literals before scanning, so documentation that mentions the word
"sorry" does not trigger a false positive.

**Certified clean (2026-06-21):** four files that carried non-classical-trio
`axiom` declarations (`Hw1_Surface`, `Wall256_Bridge`, `Wall256_MassGap`,
`Wall256_Surface1`) were quarantined and deleted. The remaining 184 lean files
pass `audit_sorry.py` with exit code 0.

Axiom footprint of every registered brick: `{propext, Classical.choice,
Quot.sound}` — the classical trio only. No `sorry`, no `admit`, no
`native_decide`, no research-grade axioms.
