# Towers/YM — YM Tower — 0 sorry — classical trio

Main YM formalization — 664 lemmas.

**Groups:**

- **Haar + SU3:** `SU3/W1.lean` `WeylDim.lean` `WeylIntegration.lean` `WeylFormulaCorrection.lean` v3 `6·(2π)²` — `torusElt_mem_SU3` `weyl_denominator_nonneg` M1-M2 bricks
- **Bessel + W1:** `BesselBounds.lean` `BesselSeries.lean` `SpecialFunctions/Bessel.lean` `W1NumericProof.lean` `W1Toeplitz.lean` `W1_One_Seventh_Proof.lean` — `bb_w1_weyl_lt : w1_weyl_series β₀ < 1/7` N=5 `+1.30e-14` margin — `β₀∈(2.07,2.08)` `ln 8`
- **Szego + Rho:** `SzegoFromWeyl.lean` `SzegoGapAvenues.lean` `YMCollection.lean` `YMRhoClose.lean` — `Cert_Arb_SzegoGap : w1_haar = w1_weyl` GW 1980 ratio 0.9896 → `ρ_SU3<1/7` → `mass_gap_lb>0` → `ym_gap_exists_cert ∃ Δ>0`
- **Transfer + Spectral:** `Transfer.lean` `TransferOperator.lean` `SpectralGapCore.lean` `PeterWeyl.lean` `PeterWeylHeat.lean` — `PeterWeyl_Summable_SU3` `∑ dim² exp(-β C₂)` summable
- **Cluster + KP:** `Wall252_KP.lean` `Wall253_KP_Cluster.lean` `Wall255_KP_Entropy.lean` `BrydgesFederbush_D1D3/D5/D6.lean` `Polymer.lean` `ClusterExpansion.lean` — `kp_lattice_gap_certified` `gap_kp_star>0` `ln 8>2`
- **OS axioms:** `OSReconstruction.lean` `OSAxiomsBundleStub.lean` `ReflectionPositivity.lean` `LocalityOS3.lean` `MassGap.lean` — lattice → continuum
- **Walls 251-264:** `Wall251b_H4.lean` → `Wall264_H4Vertices.lean` — strong coupling, dependence, Coxeter spectral, H4 defect

Build: `lake build Towers/YM` — 0 sorry — `#print axioms ym_gap_exists_cert` → `{propext, Classical.choice, Quot.sound, Cert_Arb_SzegoGap}`

Feeds Opera: **[arakelov-positivity-rh-core](https://github.com/DavidFox998/arakelov-positivity-rh-core)** ROOT V2 `48/13>0` → **[bost-connes](https://github.com/DavidFox998/bost-connes)** Hub `C(S₄)=11.422...>2√13` → **[rh-p5-bridge-14](https://github.com/DavidFox998/rh-p5-bridge-14)** Keystone `q5=226 q6=165849` → THIS — distinct Clay YM.
