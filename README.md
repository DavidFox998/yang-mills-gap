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

## Opera Numerorum — 13 repos — PUBLIC — condensed 19→1 — Routes A-D → single riemann-hypothesis-four-routes

[arakelov-positivity-rh-core](https://github.com/DavidFox998/arakelov-positivity-rh-core) — ROOT V2 — Arakelov height ω²=48/13>0 ; Zoe-M*, M4 10^4000 boundary — provides height input all RH voices reuse
[rh-p5-bridge-14](https://github.com/DavidFox998/rh-p5-bridge-14) — Keystone — q5=226, q6=165849, cf_bound=82829 — reduces infinite S_a0 to finite S14 ; closes BSD_143_PROVED → RiemannHypothesis — condensed single checkout 6cefaf3 PR78 verify ensemble green da3b943c662f vs lock 6ec00281c55d lake build Towers 0
[riemann-hypothesis-four-routes](https://github.com/DavidFox998/riemann-hypothesis-four-routes) — Four Routes — PUBLICATION WORKSPACE replaces Routes A-D — RH Core, P5 bridge, four independent formal routes preserved at exact revisions one toolchain one RH predicate — Route A Act I Abbes-Ullmo ω²=48/13>0 Siegel zero → negative height, Route B Act II Kim-Sarnak λ1≥975/4096 Selberg=Bost-Connes GRH X0(143)→RH 35pp BC6, Route C Act III Littlewood Ω exp(c√(log t / log log t)) beats (log t)² zero repulsion, Route D Act IV Dirichlet jitter ‖p·a_q‖<1/p 35 brothers collision-free swarming orbit stability Re=1/2 — all CLOSED via S4 — 7ce83ae
[bost-connes](https://github.com/DavidFox998/bost-connes) — Arithmetic hub — C(S4)=11.422...>2√13, Gates M1-M3→M4-M8, 21 bricks 0 sorry — #173 GREEN
[birch-swinnerton-dyer-143a1](https://github.com/DavidFox998/birch-swinnerton-dyer-143a1) — BSD 143a1 — rank 1, Heegner point (4,6), L(143a1,1)≠0, |Sha|=1 — worked example M1-M5 arithmetic in action
[lindelof-hypothesis-143](https://github.com/DavidFox998/lindelof-hypothesis-143) — Lindelöf for X0(143) — GRH → μ=0 → |ζ(½+it)|=O(t^ε) unconditional via S4
[eutheos-property](https://github.com/DavidFox998/eutheos-property) — Barrier bypass — 1419=3*11*43, 35 brothers ≡153 mod 211, barriers BGS/RR/AW all PASS — P vs NP study side
[poincare-spectral](https://github.com/DavidFox998/poincare-spectral) — Spectral gap — S³/I*, q=1/8, tail_26s10⁻²⁰, spectral_gap>0 — decidable instance of undecidable gap problem
[p-vs-np](https://github.com/DavidFox998/p-vs-np) — P vs NP mechanics — 225 bricks, ConductorHash, conditional SAT∉P→P≠NP — DOI 10.5281/zenodo.21303093
[hodge-abelian-boundaries](https://github.com/DavidFox998/hodge-abelian-boundaries) — Hodge obstructions — 200 measured rank obstructions for g=3,4,5 ; observed_rank>criterionBound
[yang-mills-gap](https://github.com/DavidFox998/yang-mills-gap) — ← this repo — Yang-Mills mass gap — SU(2) on R⁴, p<1/7, Δ>0, Wilson area law — same gap as C(S4)-2√13
[navier-stokes](https://github.com/DavidFox998/navier-stokes) — Navier-Stokes — Path A ESS backward uniqueness + Path B 120-cell H¹ balance — NS_M6_PROVED, no blowup
[zerobeacon](https://github.com/DavidFox998/zerobeacon) — MCP server — 1000 collision-proof tools; beacon 1d2c7a5b, m4.out = Complete: True
[beal-conjecture](https://github.com/DavidFox998/beal-conjecture) — Beal Level 26 — beal-v38 EQUIV:3 a2a23292 PR25 792b3f8 chartOfModelTrue_injective_from_Ei_constraint B=1 nonzero Y³≠0 Y³ outside cusp centreNormalPoly (X³-1)0 outside I² centreAlphaBound 2 0=1 X+V² outside cusp ann(1+Y·S³)≠ann(X²) [propext,choice,Quot.sound] 7 thm 355 + beal-v39-even 1fc6071→6f921f45 — www.beal-conjecture.com — DOI 10.5281/zenodo.23120540 superseded by 02728795 — pattern for opera 19→1
[opera-sieve](https://github.com/DavidFox998/opera-sieve) — Canonical sieve for S(alpha_0=299+π/10): computational + Lean verification
[morningstar-project](https://github.com/DavidFox998/morningstar-project) — Morning Star: machine certification for GRH(X_0(143)) and BSD(J_0(143)) — 476 equations, CLAY-sealed
[Certifications](https://github.com/DavidFox998/Certifications) — Machine-checked Lean 4 audit certificates — Morning Star Project
[birch-swinnerton-dyer-143](https://github.com/DavidFox998/birch-swinnerton-dyer-143) — BSD 143 — unconditional BSD for 143a1 — Rank=ord_L=1



ORCID: [0009-0008-1290-6105](https://orcid.org/0009-0008-1290-6105) · Archive: [pistus-theoria](https://github.com/DavidFox998/pistus-theoria) — `OperaNumerorum_MasterEquations.pdf SHA 7f6b31b4`
**Ensemble:** `sha256:e1617bc96018da4577f153f2e0cd8cc4eda1183434a9624b6cefaedc655db6c5` · hub [`rh-p5-bridge-14`](https://github.com/DavidFox998/rh-p5-bridge-14) · anchor `d04e4bd1`
## Author

David J. Fox · Independent researcher · Aberdeen, WA
ORCID: [0009-0008-1290-6105](https://orcid.org/0009-0008-1290-6105) · Opera Numerorum — 2026

```
