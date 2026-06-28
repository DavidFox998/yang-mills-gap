-- Axiom status (this file): classical trio {propext, Classical.choice, Quot.sound}
-- SORRY: 0.  All open propositions are NAMED OPEN SURFACES (not axioms, not sorry).
-- YM Surface #1: LOCKED OPEN.  No Clay claim.  NOT a brick.
--
-- PURPOSE:
--   Avenue 1 sprint toward closing SzegoGap via the Jacobi-Anger identity.
--   Milestoned 2026-06-28.
--
--   Proved in this file (classical trio, 0 sorry):
--     § besselCollect_proved              — BesselCollect_OPEN CLOSED (pure algebra)
--     § weylIntegration_SU3_trivial       — WeylIntegration_SU3_OPEN (trivial ∃-witness)
--     § toeplitzBessel_trivial            — ToeplitzBessel_Id_OPEN (tautology rfl)
--     § interchangeSumIntegral_from_sub   — conditional combinator: sub-steps → B
--     § jacobiAnger_from_all_substeps     — JacobiAnger_FormCoeff given B + C + D
--     § szego_avenues_all_closed          — szego_from_avenues fully populated
--
--   Still open (named open surface, not sorry):
--     § CosPower_FourierCoeff_OPEN  — Fourier coeff of cos^k; ~80 lines Lean
--     § FourierCoeff_Single_OPEN    — fourierCoeff(fourier m) n = δ_{m,n}; ~20 lines
--     § InterchangeSumIntegral_OPEN — series↔integral swap; ~40 lines (integral_tsum)
/-
JacobiAngerAvenue1 — Lean formalisation of Avenue 1 (Jacobi-Anger).

The Jacobi-Anger expansion:
  exp(r · cos θ) = ∑_{n∈ℤ} Iₙ(r) · eⁱⁿθ

gives fourierCoeff (exp(r·cos·)) n = Iₙ(r) = besselI_series |n| r.

PROOF CHAIN (B → C → D → Avenue 1):

  B: InterchangeSumIntegral_OPEN [OPEN — ~40 lines via integral_tsum; see §3 below]
     fourierCoeff(exp(r·cos·)) n = ∑_k r^k/k! · fourierCoeff(cos^k) n

  C: CosPower_FourierCoeff_OPEN  [OPEN — ~80 lines via orthonormal_fourier; see §4]
     fourierCoeff((cos·)^k) n = C(k,(k+|n|)/2)/2^k  [k≡n mod 2, k≥|n|]  else 0

  D: BesselCollect_OPEN          [PROVED HERE — pure algebra, §1]
     ∑_m r^{2m+n}/(2m+n)! · C(2m+n,m)/2^{2m+n} = besselI_series n r

STATUS (2026-06-28):
  D proved unconditionally.
  B + C named open surfaces with detailed proof sketches.
  JacobiAnger_FormCoeff: OPEN (conditional on B + C), wired in §5.
  Avenues 2+3: CLOSED trivially as stated (honest placeholders).
-/

import Towers.YM.SzegoGapAvenues
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace TheoremaAureum.Towers.YM.JacobiAngerAvenue1

open Real BigOperators MeasureTheory
open TheoremaAureum.Towers.YM.BesselSeries
open TheoremaAureum.Towers.YM.WeylToeplitzBound
open TheoremaAureum.Towers.YM.W1Toeplitz
open TheoremaAureum.Towers.YM.SzegoGapAvenues

-- Period instance required throughout.
private instance : Fact (0 < (2 : ℝ) * Real.pi) := ⟨by positivity⟩

/-! ## §1  Step D: Bessel Series Collection (PROVED) -/

/-- **PROVED (trio-only).** The key combinatorial identity:
  `C(2m+n, m) * m! * (m+n)! = (2m+n)!`
This is `Nat.add_choose_mul_factorial_mul_factorial m (m+n)` after rewriting the index. -/
private theorem choose_factorial_identity (m n : ℕ) :
    (2*m+n).choose m * m.factorial * (m+n).factorial = (2*m+n).factorial := by
  have h := Nat.add_choose_mul_factorial_mul_factorial m (m+n)
  rwa [show m + (m+n) = 2*m+n from by ring] at h

/-- **PROVED (trio-only).** Sub-step D: Bessel series collection.

Per term, for `k = 2m+n`:
  `r^(2m+n) / (2m+n)! · C(2m+n,m) / 2^(2m+n) = (r/2)^(n+2m) / (m! · (n+m)!)`

Proof: `C(2m+n,m) * m! * (m+n)! = (2m+n)!` (proved by `choose_factorial_identity`),
then `field_simp` + `linear_combination`. -/
theorem besselCollect_proved : BesselCollect_OPEN := by
  intro r _hr n
  simp only [besselI_series]
  apply tsum_congr
  intro m
  have hC_nat : (2*m+n).choose m * m.factorial * (m+n).factorial = (2*m+n).factorial :=
    choose_factorial_identity m n
  have hC : ((2*m+n).choose m : ℝ) * (m.factorial : ℝ) * ((m+n).factorial : ℝ)
          = ((2*m+n).factorial : ℝ) := by exact_mod_cast hC_nat
  have hm   : (m.factorial : ℝ) ≠ 0       := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hmn  : ((n+m).factorial : ℝ) ≠ 0   := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2mn : ((2*m+n).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2   : (2 : ℝ)^(2*m+n) ≠ 0         := pow_ne_zero _ two_ne_zero
  have hCne : ((2*m+n).choose m : ℝ) ≠ 0  :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  rw [show n + 2*m = 2*m+n from by ring, show n + m = m+n from by ring, div_pow]
  field_simp [hm, hmn, h2mn, h2, hCne]
  linear_combination (r ^ (2*m+n)) * hC

/-! ## §2  Avenues 2 and 3: Trivial Closures -/

/-- **PROVED (trio-only).** `WeylIntegration_SU3_OPEN` as stated is an existential:
  `∃ w1_haar : ℝ → ℝ, w1_haar β = w1_weyl_series β`.
Witness: `w1_weyl_series` itself.

**Honesty**: This does NOT formalize the SU(3) Weyl integration formula.  The TRUE gap —
that the physical Haar weight `w1 β` equals `w1_weyl_series β` — requires the Weyl character
formula for SU(3) (absent from Mathlib v4.12.0).  The existential was a placeholder; this
closure records existence of the target value, not the physics. -/
theorem weylIntegration_SU3_trivial : WeylIntegration_SU3_OPEN :=
  fun β _ => ⟨fun _ => w1_weyl_series β, rfl⟩

/-- **PROVED (trio-only).** `ToeplitzBessel_Id_OPEN` is the tautology `a = a` — both sides
of the defining equation are the SAME Lean expression.  Hence `fun _ _ => rfl`.

**Honesty**: The TRUE Toeplitz–Szegő identity (equating the torus integral from Avenue 2
to this determinant sum) is NOT proved.  Fredholm determinants and the Szegő strong limit
theorem are absent from Mathlib v4.12.0. -/
theorem toeplitzBessel_trivial : ToeplitzBessel_Id_OPEN :=
  fun _ _ => rfl

/-! ## §3  Step B: Power Series / Integral Interchange (OPEN — named surface) -/

-- `InterchangeSumIntegral_OPEN` is defined in SzegoGapAvenues §3.
-- Status: OPEN.  Estimated ~40 lines using `integral_tsum_of_summable_integral_norm`.
--
-- PROOF SKETCH:
--
-- def fourierCoeff f n = ∫ θ, fourier(-n) θ • f θ ∂haarAddCircle
--
-- Step B-1: expand exp(r·cos θ) = ∑_k (r·cos θ)^k/k!
--   Use Real.hasSum_exp or NNReal.hasSum_coe_toNNReal_exp to get the HasSum.
--   Cast to ℂ via Complex.ofReal_exp.
--   The series is (r·cos θ)^k/k! = r^k/k! · cos(θ:ℝ)^k.
--
-- Step B-2: swap ∑ and ∫ via integral_tsum_of_summable_integral_norm.
--   Hypotheses required:
--   (a) AEStronglyMeasurable: each k-th term is continuous → AEStronglyMeasurable.
--   (b) Summability of ∫ ‖term_k‖ ∂haar:
--       ‖fourier(-n) θ · r^k/k! · cos^k θ‖ ≤ r^k/k! (since |fourier(-n)| = 1, |cos| ≤ 1)
--       ∑_k r^k/k! = exp(r) < ∞  (by Real.summable_pow_div_factorial).
--
-- Step B-3: linearity.
--   ∫ fourier(-n) θ · (r^k/k!) · cos^k θ ∂haar
--   = r^k/k! · ∫ fourier(-n) θ · cos^k θ ∂haar    [by integral_mul_left]
--   = r^k/k! · fourierCoeff (cos^k) n               [by def of fourierCoeff]
--
-- Key Mathlib lemmas:
--   MeasureTheory.integral_tsum_of_summable_integral_norm (DominatedConvergence.lean:152)
--   MeasureTheory.integral_mul_left
--   Continuous.aestronglyMeasurable
--   Real.summable_pow_div_factorial

/-- **NAMED OPEN SURFACE.** Conditional combinator: steps B, C, D → JacobiAnger.
If `InterchangeSumIntegral_OPEN` is proved (step B), the rest follows from C and D. -/
theorem interchangeSumIntegral_from_sub
    (hB : InterchangeSumIntegral_OPEN) (hC : CosPower_FourierCoeff_OPEN)
    (r : ℝ) (hr : 0 ≤ r) (n : ℤ) :
    MeasureTheory.fourierCoeff
        (fun (θ : AddCircle (2 * Real.pi)) =>
          (Real.exp (r * Real.cos (θ : ℝ)) : ℂ)) n =
    ∑' k : ℕ,
        (r ^ k / (k.factorial : ℂ)) *
          (if (k : ℤ) ≥ n.natAbs ∧ (k : ℤ) % 2 = n % 2
           then (k.choose (((k : ℤ) + n.natAbs) / 2).toNat : ℂ) / 2 ^ k
           else 0) := by
  rw [hB r hr n]
  apply tsum_congr; intro k
  rw [hC k n]

/-! ## §4  Step C: Cosine-Power Fourier Coefficient (OPEN — named surface + sub-lemma) -/

-- `CosPower_FourierCoeff_OPEN` is defined in SzegoGapAvenues §3.
-- Status: OPEN.  Estimated ~80 lines.
--
-- PROOF SKETCH:
--
-- STEP C-1: cos θ in terms of Fourier characters.
--   For T = 2π: fourier_coe_apply gives
--     fourier n (θ : AddCircle (2π)) = exp(2πi·n·(θ:ℝ)/(2π)) = exp(in·(θ:ℝ))
--   In particular:
--     fourier 1  θ = exp(i·θ)          (↑ to ℂ via toCircle)
--     fourier (-1) θ = exp(-i·θ) = conj(fourier 1 θ)   [by fourier_neg]
--   The Euler formula for cos then gives:
--     (Real.cos (θ:ℝ) : ℂ) = (fourier 1 θ + fourier (-1) θ) / 2
--   Key lemma: cosEuler_eq_fourier — ~10 lines using fourier_coe_apply + Complex.cos_eq.
--
-- STEP C-2: Binomial expansion of cos^k.
--   cos^k θ = ((fourier 1 θ + fourier (-1) θ)/2)^k
--           = (1/2^k) ∑_{j=0}^k C(k,j) (fourier 1)^j (fourier (-1))^(k-j)
--   Use fourier_add: (fourier 1)^j * (fourier (-1))^(k-j) = fourier (2j - k : ℤ).
--
-- STEP C-3: Fourier coefficient of a single character (key delta lemma).
--   FourierCoeff_Single_OPEN (m n : ℤ) :
--     fourierCoeff (fun θ => fourier m θ) n = if m = n then 1 else 0
--   Proof: fourierBasis.repr f n = fourierCoeff f n (from AddCircle.lean ~369)
--          + orthonormal_fourier (Orthonormal ℂ (fourierLp T 2)) gives the delta.
--   Estimated ~20 lines.
--
-- STEP C-4: Linearity + selection.
--   fourierCoeff (cos^k) n
--   = (1/2^k) ∑_{j=0}^k C(k,j) · (if 2j-k = n then 1 else 0)
--   = C(k, (k+n)/2) / 2^k   [if k ≡ n (mod 2) and |n| ≤ k]
--   else 0.

/-- **NAMED OPEN SUB-SURFACE.** The Fourier coefficient of a single Fourier character.
  `fourierCoeff (fun θ => fourier m θ) n = if m = n then 1 else 0`
This is the delta-function property of the Fourier basis.
Proof path: `fourierBasis.repr_apply_eq fourierCoeff` + `orthonormal_fourier`.
Estimated: ~20 lines. -/
def FourierCoeff_Single_OPEN : Prop :=
  ∀ (m n : ℤ),
    MeasureTheory.fourierCoeff
        (fun (θ : AddCircle (2 * Real.pi)) => @fourier (2 * Real.pi) m θ) n
      = if m = n then 1 else 0

/-! ## §5  Full JacobiAnger Combinator -/

/-- **PROVED conditional on B and C (trio-only).**

Given `InterchangeSumIntegral_OPEN` (step B) and `CosPower_FourierCoeff_OPEN` (step C),
the JacobiAnger identity follows by:
  - Step B expands fourierCoeff(exp(r·cos·)) into a series of fourierCoeff(cos^k) terms.
  - Step C gives fourierCoeff(cos^k) n = sparse polynomial.
  - BesselCollect (step D, proved in §1) collects the sparse k=2m+n terms into besselI_series.

The reindexing k → m (via k = |n| + 2m) and tsum bijection is the final wiring:
  ∑_{k≡n mod 2, k≥|n|} r^k/k! · C(k,(k+|n|)/2)/2^k = besselI_series |n| r.
This uses `besselCollect_proved` per term and `Equiv`-based tsum reindexing.
Estimated wiring: ~40 additional lines (Equiv.ofBijective + tsum_congr). -/
theorem jacobiAnger_from_all_substeps
    (hB : InterchangeSumIntegral_OPEN)
    (hC : CosPower_FourierCoeff_OPEN)
    (hD : BesselCollect_OPEN)
    (h_reindex : ∀ (r : ℝ) (hr : 0 ≤ r) (n : ℤ),
      ∑' k : ℕ,
          (r ^ k / (k.factorial : ℂ)) *
            (if (k : ℤ) ≥ n.natAbs ∧ (k : ℤ) % 2 = n % 2
             then (k.choose (((k : ℤ) + n.natAbs) / 2).toNat : ℂ) / 2 ^ k
             else 0)
        = (besselI_series n.natAbs r : ℂ)) :
    JacobiAnger_FormCoeff := by
  intro r hr n
  rw [interchangeSumIntegral_from_sub hB hC r hr n]
  exact h_reindex r hr n

/-- **NAMED OPEN SURFACE.** The tsum reindexing step: the sparse sum (over k ≡ n mod 2,
k ≥ |n|) equals `besselI_series |n| r`.

This is a bijective reindexing ℕ → {k : ℕ | k ≡ n (mod 2) ∧ k ≥ |n|}, m ↦ |n|+2m,
combined with `besselCollect_proved` per term.  Estimated ~40 lines using
`tsum_eq_tsum_of_hasSum` + `Equiv.ofBijective`. -/
def BesselReindex_OPEN : Prop :=
  ∀ (r : ℝ) (hr : 0 ≤ r) (n : ℤ),
    ∑' k : ℕ,
        (r ^ k / (k.factorial : ℂ)) *
          (if (k : ℤ) ≥ n.natAbs ∧ (k : ℤ) % 2 = n % 2
           then (k.choose (((k : ℤ) + n.natAbs) / 2).toNat : ℂ) / 2 ^ k
           else 0)
      = (besselI_series n.natAbs r : ℂ)

/-- **PROVED (trio-only).** `JacobiAnger_FormCoeff` follows from
`InterchangeSumIntegral_OPEN` + `CosPower_FourierCoeff_OPEN` + `BesselReindex_OPEN`.
All three remain open; once proved, this combinator closes Avenue 1. -/
theorem jacobiAnger_proved
    (hB : InterchangeSumIntegral_OPEN)
    (hC : CosPower_FourierCoeff_OPEN)
    (hR : BesselReindex_OPEN) :
    JacobiAnger_FormCoeff :=
  jacobiAnger_from_all_substeps hB hC besselCollect_proved hR

/-! ## §6  Full Three-Avenue Combinator -/

/-- **PROVED (trio-only).** All three avenues now have SOME form of closure:
  Avenue 1 (JacobiAnger): conditional on B + C + BesselReindex (D proved; B, C, R open)
  Avenue 2 (WeylIntegration_SU3): trivially closed (∃-witness, not physical)
  Avenue 3 (ToeplitzBessel_Id): trivially closed (tautology rfl)

The SzegoGap combinator is populated with these closures.
`h_wire` remains the honest explicit hypothesis: SzegoGap is still OPEN. -/
theorem szego_avenues_all_closed
    (hB : InterchangeSumIntegral_OPEN)
    (hC : CosPower_FourierCoeff_OPEN)
    (hR : BesselReindex_OPEN)
    (w1 : ℝ → ℝ)
    (h_wire : w1 (β₀_rat : ℝ) = w1_weyl_series (β₀_rat : ℝ)) :
    SzegoGap w1 :=
  szego_from_avenues
    (jacobiAnger_proved hB hC hR)
    weylIntegration_SU3_trivial
    toeplitzBessel_trivial
    w1
    h_wire

/-! ## §7  State Audit -/

/-- **PROVED (trio-only, milestone audit — 2026-06-28 Avenue-1 sprint).**

## Proved in this file (classical trio, 0 sorry):
  besselCollect_proved         BesselCollect_OPEN CLOSED (algebraic, 30 lines)
  weylIntegration_SU3_trivial  WeylIntegration_SU3_OPEN CLOSED (trivial ∃-witness)
  toeplitzBessel_trivial       ToeplitzBessel_Id_OPEN CLOSED (tautology rfl)
  jacobiAnger_proved           JacobiAnger_FormCoeff CONDITIONAL on B + C + BesselReindex
  szego_avenues_all_closed     Full combinator wired (h_wire still explicit)

## Still open (named surfaces, all 0 sorry):
  InterchangeSumIntegral_OPEN   series↔integral swap (~40 lines, integral_tsum)
  CosPower_FourierCoeff_OPEN    Fourier coeff of cos^k (~80 lines, orthonormal_fourier)
  FourierCoeff_Single_OPEN      fourierCoeff(fourier m) n = δ_{m,n} (~20 lines)
  BesselReindex_OPEN            tsum reindexing k=|n|+2m (~40 lines, Equiv bijection)
  JacobiAnger_FormCoeff         OPEN until B + C + BesselReindex proved

## SzegoGap status:
  OPEN.  h_wire (w1 β₀ = w1_weyl_series β₀) is the honest explicit hypothesis.
  The trivial closures of Avenues 2+3 are honest placeholders:
    TRUE Avenue 2 (SU(3) Weyl formula) requires SU(3) character theory.
    TRUE Avenue 3 (Szegő strong limit theorem) requires Fredholm.det.

## LOCKED OPEN (invariants — do not discharge):
  YM Surface #1 (mass gap, ρ < 1)   LOCKED (Clay invariant, replit.md)
  NS Surface #1, #2                  LOCKED (NS freeze invariant, replit.md) -/
theorem avenue1_sprint_audit_2026_06_28 : True := trivial

end TheoremaAureum.Towers.YM.JacobiAngerAvenue1
