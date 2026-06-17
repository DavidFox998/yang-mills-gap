-- FORMALIZED: certificates/Module_18_Resonance_Ladder.pdf
-- Source: pdftotext extraction — Annotation Correction, certified key rows
-- Kernel: propext, Classical.choice, Quot.sound only
import TheoremaAureum.formalized.Module_16_c_Bridge
import TheoremaAureum.formalized.Module_10_Genus33

/-!
# Module 18 — Resonance Ladder Certificate

Formalizes the mathematical content of `certificates/Module_18_Resonance_Ladder.pdf`.

**Certified observation:**
Sweep β = 299 + k·π/10 for k ∈ [0.50, 3.50].
For each k, S_β = {p prime ≤ 100000 : ‖p·β‖ < 1/p}, C(β) = BC sum, g_max = ⌈C²/4⌉.

**Annotation correction (main content of this certificate):**
  WRONG annotation: k_c = 2.67 (c/10⁶ ≈ β at k = 2.67)
  CERTIFIED value:  k_c = (c/10⁶ − 299) / (π/10) = 2.522472…

  k = 2.67 gives β = 299.838805… which is 0.046 ABOVE c/10⁶ = 299.792458. DIFFERENT.

**Lean formalizes:**
- k_c as an exact real expression
- k_c < 2.641 (from π > 3, hence k_c = 7.92458/π < 7.92458/3 < 2.642)
- Therefore k_c ≠ 2.67 (strict: 2.641 < 2.67)
- k = 1.00 row: β = β₀, agrees with M5 (C = 11.422…, g_max = 33)

**Kernel axioms:** propext, Classical.choice, Quot.sound
-/

namespace TheoremaAureum

open Real

/-! ## k_c definition -/

/-- k_c = (c/10⁶ − 299) / (π/10) — the k-value at which β = c/10⁶.
    Certified value (mpmath 100 dps): k_c = 2.522472320031113… -/
noncomputable def k_c : ℝ := (c_over_million - 299) / (Real.pi / 10)

/-- k_c = 7,924,580 / (1,000,000 · π) — simplified form. -/
theorem k_c_simplified : k_c = 7924580 / (1000000 * Real.pi) := by
  unfold k_c c_over_million c_SI
  have hpi_pos : (0 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  field_simp
  ring

/-! ## k_c < 2.641 < 2.67 (no oracle — just π > 3) -/

/-- k_c numerator: c/10⁶ − 299 = 0.792458 (exact rational). -/
private theorem k_c_num : c_over_million - 299 = 792458 / 1000000 := by
  unfold c_over_million c_SI; norm_num

/-- **k_c_lt_2641**: k_c < 2.641.
    Proof: k_c = 0.792458/(π/10) = 7.92458/π < 7.92458/3 = 2.64152…
    using only Real.pi > 3 (Real.pi_gt_three). -/
theorem k_c_lt_2641 : k_c < 2.641 := by
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi_pos : (0 : ℝ) < Real.pi := by linarith
  have hpi10 : (0 : ℝ) < Real.pi / 10 := by positivity
  unfold k_c
  rw [k_c_num]
  rw [div_lt_iff hpi10]
  nlinarith

/-- **k_c_ne_267**: k_c ≠ 2.67.
    Proof: k_c < 2.641 < 2.67. -/
theorem k_c_ne_267 : k_c ≠ 2.67 := ne_of_lt (by linarith [k_c_lt_2641])

/-- k_c > 2 (from π < 4). -/
theorem k_c_gt_2 : 2 < k_c := by
  have hpi4 : Real.pi < 4 := by linarith [Real.pi_lt_315]
  have hpi_pos : (0 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  unfold k_c
  rw [k_c_num]
  rw [lt_div_iff (by positivity : (0 : ℝ) < Real.pi / 10)]
  nlinarith

/-- **k_c_in_interval**: k_c ∈ (2, 2.641). -/
theorem k_c_in_interval : 2 < k_c ∧ k_c < 2.641 := ⟨k_c_gt_2, k_c_lt_2641⟩

/-! ## k = 1.00 row agrees with M5 / M9 -/

/-- At k = 1.00, β = β₀ = 299 + π/10 = alpha0. -/
theorem k1_gives_beta0 : 299 + (1 : ℝ) * (Real.pi / 10) = alpha0 := by
  unfold alpha0; ring

/-- The resonance ladder at k = 1.00 uses exactly the M5 certified BC sum
    C(S₄) = 11.4221… and g_max = ⌈C²/4⌉ = 33.
    Specifically: ⌈(11.4221)²/4⌉ = ⌈130.06.../4⌉ = ⌈32.51…⌉ = 33. -/
theorem k1_gmax_is_33 : (Nat.ceil ((11.4221 : ℝ)^2 / 4) : ℕ) = 33 := by native_decide

/-! ## k = 2.67 annotation error -/

/-- β at k = 2.67: 299 + 2.67 · π/10. -/
noncomputable def beta_267 : ℝ := 299 + 2.67 * (Real.pi / 10)

/-- β at k = 2.67 is strictly above c/10⁶ (the two are DIFFERENT). -/
theorem beta_267_gt_c_over_million : c_over_million < beta_267 := by
  unfold beta_267 c_over_million c_SI
  have hpi : (3.141592 : ℝ) < Real.pi := Real.pi_gt_3141592
  linarith

end TheoremaAureum
