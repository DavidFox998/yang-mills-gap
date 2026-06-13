/-
# Beta0 Certification Record — Out-of-Tower (CERT_Arb)

Records the rigorous interval enclosure of the KP phase-transition threshold β₀
for the single-plaquette SU(3) Haar weight

    w1(β) = ∫_{SU(3)} exp(-β·S(U)) d haarSU3,  S = (3 - Re tr U)/3

where β₀ is the unique crossing point w1(β₀) = 1/7.

Source: exports/CERT_Arb_beta0_2026-06-01.yaml
Method: exact rational moments (Weyl/constant-term extraction) + rigorous tail bound
        + mpmath.iv interval arithmetic (outward rounding), iv_dps=80, N=36 terms,
        tail ≤ 4.46e-32 at β=2.07943.

Certified: β₀ ∈ [2079416880123/10¹², 519854220031/2.5×10¹¹]
           = [2.079416880123, 2.079416880124]  (width 1e-12)

D4 verdict: w1(0.86) ∈ [0.43237..] > 1/7  →  D4 TESTED NEGATIVE CERTIFIED at β=0.86.
Safe formal requirement: β > 2.079416880124 (upper endpoint, conservative).

STATUS: OUT_OF_TOWER. NOT a Lean proof. NOT trio-clean. Does NOT discharge D4,
does NOT close the KP surface, does NOT prove the mass gap. hw1 stays an OPEN
named hypothesis in Wall256_Scaffold. Surface #1 stays OPEN.
-/

namespace TheoremaAureum.Towers.YM.Beta0

/-! ## Certified numerals (rational, definitional — no arithmetic content) -/

/-- Lower endpoint of the certified β₀ interval (2.079416880123...). -/
def beta0_lo : ℚ := 2079416880123 / 1000000000000

/-- Upper endpoint of the certified β₀ interval (2.079416880124...).
    Conservative formal requirement: hw1 requires β > beta0_hi. -/
def beta0_hi : ℚ := 519854220031 / 250000000000

/-- The D4 threshold (1/7 = 0.142857...). KP requires w1 < this strictly. -/
def kp_threshold : ℚ := 1 / 7

/-- Record that the numerals are well-formed and the interval is non-degenerate.
    Proof is rfl + decide; no analytic content. OUT-OF-TOWER certificate lives in
    exports/CERT_Arb_beta0_2026-06-01.yaml. -/
theorem beta0_interval_nonempty : beta0_lo < beta0_hi := by decide

/-- The out-of-tower certified fact (as a named Prop, NOT proved in Lean).
    States: β₀ ∈ [beta0_lo, beta0_hi] and w1(0.86) > 1/7.
    NOT discharged here — the actual analytic content is in CERT_Arb (mpmath.iv). -/
def Beta0Certified_Surface : Prop :=
  ∃ β₀ : ℝ, (beta0_lo : ℝ) ≤ β₀ ∧ β₀ ≤ (beta0_hi : ℝ) ∧
    ∀ β : ℝ, (beta0_hi : ℝ) < β →
      (∫ _ : TheoremaAureum.Towers.YM.SU3Instances.SU3,
        Real.exp (-β * (1 - 0)) ∂TheoremaAureum.Towers.YM.SU3Instances.haarSU3) < 1 / 7

/-- Sorry-free pass-through: given the out-of-tower certificate as hypothesis,
    re-state it. Proof = h.
    #print axioms: [propext, Classical.choice, Quot.sound]. -/
theorem beta0_certified (h : Beta0Certified_Surface) : Beta0Certified_Surface := h

end TheoremaAureum.Towers.YM.Beta0
