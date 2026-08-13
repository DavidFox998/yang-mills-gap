# Towers/YM/SU3 — SU(3) structure

- `Polylog.lean` — polylog for heat kernel
- `Tauberian.lean` — Tauberian for spectral
- `W1.lean` — single-site weight `w1 = exp(-3β) Σ det[I_{|i-j-k|}]`
- `WeylUpperBound.lean` — Weyl dim upper bound `dim≤8·(m+n+1)³`

Provides `torusElt_mem_SU3` `diag(e^{iθ₁},e^{iθ₂},e^{-i(θ₁+θ₂)})∈SU(3)` + `weyl_denominator_nonneg` — M1-M2 — used in `WeylFormulaCorrection.lean` `6·(2π)²`.
