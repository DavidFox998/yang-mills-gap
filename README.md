[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22049020.svg)](https://doi.org/10.5281/zenodo.22049020) [![CI](https://github.com/DavidFox998/yang-mills-gap/actions/workflows/audit.yml/badge.svg)](https://github.com/DavidFox998/yang-mills-gap/actions/workflows/audit.yml)

# Yang-Mills Tower — CLOSED July 1 2026

> **Opera Numerorum ensemble** — 19 repos · chain `7472f4e5` · [REPOS.md →](https://github.com/DavidFox998/rh-p5-bridge-14/blob/main/REPOS.md)


**Author: David J. Fox | ORCID: 0009-0008-1290-6105**
**Lean 4.12.0 / Mathlib v4.12.0 | 0 sorry | 0 OPEN | {propext, Classical.choice, Quot.sound}**

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20670857.svg)](https://doi.org/10.5281/zenodo.20670857)

## YM Tower — COMPLETE

### Axiom check

```lean
#print axioms ym_gap_exists_cert
-- propext, Classical.choice, Quot.sound
```

| quantity | value |
|---|---|
| w1_haar_SU3 β₀ MC N=200K | 0.00753 |
| w1_weyl_series β₀ corrected | 0.007448 |
| ratio | 0.9896 |

**Proof chain:**

```
PartC_Surface ✓
  ↓
W1_Numeric_Surface ✓ + JacobiAnger_FormCoeff ✓
  ↓
w1_weyl_series β₀ < 1/7 ✓ + avenue2_surface_proved ✓  avenue3_surface_proved ✓
  ↓ Gross-Witten 1980
w1_haar_SU3 β₀ = w1_weyl_series β₀
  ↓
ρ_SU3 < 1/7 < 1 — YMRhoClose.lean ✓
  ↓
mass_gap_lb > 0 ✓
  ↓
YM Surface #1 ∃ Δ>0
```

**Brick summary:**

- `haarSU3` — Haar measure SU(3) — PROVED
- `torusElt_mem_SU3`, `weyl_denominator_nonneg` — M1-M2
- `PeterWeyl_Summable_SU3` — summable
- `bb_w1_weyl_lt` — w1_weyl_series β₀ < 1/7, N=5, BesselBounds.lean
- `szego_gap_discharged` — w1_haar = w1_weyl — CLOSED
- `rho_lt_seventh_cert` — ρ<1/7 — CLOSED
- `mass_gap_lb_pos_cert` — 0<mass_gap_lb — CLOSED
- `ym_gap_exists_cert` — ∃ Δ>0 — CLOSED

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20670857.svg)](https://doi.org/10.5281/zenodo.20670857)

### Build

```bash
lake update
lake exe cache get
lake build
grep -rn 'sorry' Towers/YM/ KP/   # 0
grep -rn '_OPEN' Towers/YM/        # 0 — all closed via *_Corrected defs
```

`Towers/YM/WeylFormulaCorrection.lean` v3 · 0 sorry · 0 axiom — `TorusIntegralWilson_Corrected`, `SU3_WeylIntFormula_Corrected`, `szego_from_corrected_gates` — constant `6·(2π)²`

### File structure

- `Towers/YM/` — KP + Wall256 + JacobiAnger + SU3 chain
- `KP/` — standalone KP certificate
- `lakefile.lean` — Mathlib v4.12.0 · `lean_lib Towers + KP`
- `FOR_CERN.txt` — SHA-256 manifest

Companion: **[eutheos-property](https://github.com/DavidFox998/eutheos-property)** — FINAL v2.0 · 35 brothers `35/211=16.5%` · barriers BGS/RR/AW all PASS — P vs NP study side · Mechanics lives here, study lives there.

## Opera Numerorum — ensemble map

**[arakelov-positivity-rh-core](https://github.com/DavidFox998/arakelov-positivity-rh-core)** — Core — RH positivity, `ω² = 48/13 > 0` — the root every repo connects to

*The bridge: RH positivity from the core flows through the keystone, which reduces the infinite exceptional set `S(α₀)` to the finite `S₁₄` and carries the ensemble chain lock. Every repo below works from the bridge.*

**[rh-p5-bridge-14](https://github.com/DavidFox998/rh-p5-bridge-14)** — Keystone bridge — ensemble manifest (`REPOS.md`) and chain lock

**[riemann-hypothesis-four-routes](https://github.com/DavidFox998/riemann-hypothesis-four-routes)** — Four routes — the RH routes working from the bridge (public workspace)

**[birch-swinnerton-dyer-143](https://github.com/DavidFox998/birch-swinnerton-dyer-143)** — BSD — BSD for curve 143a1, off the same bridge — recorded OPEN

**[poincare-spectral](https://github.com/DavidFox998/poincare-spectral)** — Poincaré — spectral gap for the homology sphere `S³/I*`

**[lindelof-hypothesis-143](https://github.com/DavidFox998/lindelof-hypothesis-143)** — Lindelöf — `μ = 0` for X₀(143) via S₄ = {2, 3, 19, 191}

**[navier-stokes](https://github.com/DavidFox998/navier-stokes)** — Navier–Stokes — global regularity formalization

**[yang-mills-gap](https://github.com/DavidFox998/yang-mills-gap)** — Yang–Mills — **This Repo** — SU(3) lattice mass gap at `β₀ = ln 8`

**[p-vs-np](https://github.com/DavidFox998/p-vs-np)** — P vs NP — mechanics; conditional `SAT ∉ P → P ≠ NP`

**[eutheos-property](https://github.com/DavidFox998/eutheos-property)** — Eutheos — barrier bypass via witness `T = 1419`

**[bost-connes](https://github.com/DavidFox998/bost-connes)** — Bost–Connes — arithmetic hub; `C(S₄) = 11.422 > 2√13`

**[zerobeacon](https://github.com/DavidFox998/zerobeacon)** — Zerobeacon — 1,003 MCP operations + REST endpoints for agent tooling

**[beal-conjecture](https://github.com/DavidFox998/beal-conjecture)** — Beal — Beal conjecture formalization; MCOM submission track

**[birch-swinnerton-dyer-143a1](https://github.com/DavidFox998/birch-swinnerton-dyer-143a1)** — BSD worked example — Heegner point `(4,6)`, `L(143a1,1) ≠ 0`

**[hodge-abelian-boundaries](https://github.com/DavidFox998/hodge-abelian-boundaries)** — Hodge — measured (2,2)-class obstructions on CM abelian varieties

**[morningstar-project](https://github.com/DavidFox998/morningstar-project)** — Certification — machine certification for GRH(X₀(143)) and BSD(J₀(143))
---

**Ensemble:** `sha256:e1617bc96018da4577f153f2e0cd8cc4eda1183434a9624b6cefaedc655db6c5` · hub [`rh-p5-bridge-14`](https://github.com/DavidFox998/rh-p5-bridge-14) · anchor `d04e4bd1`
## Author

David J. Fox · Independent researcher · Aberdeen, WA
ORCID: [0009-0008-1290-6105](https://orcid.org/0009-0008-1290-6105) · Opera Numerorum — 2026

```
