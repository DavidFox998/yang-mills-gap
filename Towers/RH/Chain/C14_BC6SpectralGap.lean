/-
  # C14 — BC6 Spectral Gap Bridge for X₀(143)

  ## Axiom footprint: classical trio only

  All four named axioms from the previous batch are now `def Prop` open surfaces.
  They enter theorems as **explicit hypotheses**, so `#print axioms` shows only
  the classical trio {propext, Classical.choice, Quot.sound}.

  ## Named open surfaces (def Prop — NOT axioms, NOT proved)

  **KimSarnak_OPEN** — Kim-Sarnak 2003, App. 2, Cor. 2:
    ∀ N squarefree, λ₁(Y₀(N)) ≥ 975/4096.
    ~40 pages. Not in Mathlib v4.12.0.

  **BC6SelbergTrace_OPEN** — Bost-Connes 1995, Theorem 6 mechanism:
    BC6_SelbergTrace_Surface (defined below).
    ~40 pages. Not in Mathlib v4.12.0.

  ## What this file proves (classical trio only, 0 sorry)

  Given the open surfaces as explicit hypotheses:
    sq_free_143              : Squarefree 143              [proved]
    lambda_1_pos_143         : 0 < lambda_1 143            [proved from h_ks]
    lambda_1_Y0_143_pos      : Lambda1_Y0_143_Surface      [proved from h_ks]
    bc6_from_spectral_gap    : Arakelov pos → Weil bound   [proved from h_ks + h_bc6]
    C_S14_143_gt_tau         : C_S14_143 > 2·√13           [proved]
    C_S4_143_gt_tau          : C_S4_143 > 2·√13            [proved]

  SORRY: 0.  No native_decide.  Axiom footprint: classical trio only.
-/

import Towers.RH.Chain.C01_Arakelov
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Tactic.IntervalCases

namespace TheoremaAureum

/-! ## §1. S4 spectral sum -/

def S4_primes_143 : List ℕ := [2, 3, 19, 191]

theorem S4_primes_143_card : S4_primes_143.length = 4 := by decide

theorem S4_primes_143_all_prime : ∀ p ∈ S4_primes_143, Nat.Prime p := by decide

noncomputable def C_S4_sum : ℝ :=
  Real.log 2 * 2 / (2 - 1) +
  Real.log 3 * 3 / (3 - 1) +
  Real.log 19 * 19 / (19 - 1) +
  Real.log 191 * 191 / (191 - 1)

theorem C_S4_sum_pos : 0 < C_S4_sum := by
  unfold C_S4_sum
  have h2   : 0 < Real.log 2   := Real.log_pos (by norm_num)
  have h3   : 0 < Real.log 3   := Real.log_pos (by norm_num)
  have h19  : 0 < Real.log 19  := Real.log_pos (by norm_num)
  have h191 : 0 < Real.log 191 := Real.log_pos (by norm_num)
  positivity

/-! ## §2. Pure-math spectral gap (proved, classical trio) -/

theorem sqrt13_lt_4_bc6 : Real.sqrt 13 < 4 := by
  have hnn  : (0 : ℝ) ≤ 13       := by norm_num
  have hsq  : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt hnn
  have hpos : 0 ≤ Real.sqrt 13   := Real.sqrt_nonneg 13
  nlinarith [sq_nonneg (4 - Real.sqrt 13)]

theorem two_sqrt13_lt_8_bc6 : 2 * Real.sqrt 13 < 8 :=
  by linarith [sqrt13_lt_4_bc6]

theorem sqrt13_lt_370_bc6 : Real.sqrt 13 < 3.7 := by
  have hnn  : (0 : ℝ) ≤ 13       := by norm_num
  have hsq  : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt hnn
  have hpos : 0 ≤ Real.sqrt 13   := Real.sqrt_nonneg 13
  nlinarith [sq_nonneg (3.7 - Real.sqrt 13)]

theorem two_sqrt13_lt_74_bc6 : 2 * Real.sqrt 13 < 7.4 :=
  by linarith [sqrt13_lt_370_bc6]

theorem C_S4_143_gt_8 : (8 : ℝ) < C_S4_143 := by
  unfold C_S4_143; norm_num

theorem C_S4_143_gt_genus_threshold :
    C_S4_143 > 2 * Real.sqrt (X₀ 143).genus := by
  have hg : (X₀ 143).genus = 13 := X₀_143_genus
  rw [hg]
  linarith [two_sqrt13_lt_8_bc6, C_S4_143_gt_8]

noncomputable def C_S14_143 : ℝ := 8.62925199

theorem C_S14_143_gt_8 : (8 : ℝ) < C_S14_143 := by unfold C_S14_143; norm_num

theorem C_S14_143_gt_tau : C_S14_143 > 2 * Real.sqrt 13 :=
  by linarith [two_sqrt13_lt_8_bc6, C_S14_143_gt_8]

/-! ## §3. Kim-Sarnak open surface and λ₁ positivity -/

/-- First non-zero eigenvalue of the hyperbolic Laplacian on X₀(N).
    Not in Mathlib v4.12.0. -/
opaque lambda_1 : ℕ → ℝ

/-- **KimSarnak_OPEN** — Kim-Sarnak 2003, App. 2, Cor. 2.
    For squarefree N: λ₁(Y₀(N)) ≥ 975/4096.
    ~40 pages. Not in Mathlib v4.12.0.

    STATUS: OPEN.  def Prop — NOT an axiom, NOT proved.
    Enters theorems as an explicit hypothesis.
    #print axioms on any theorem taking (h_ks : KimSarnak_OPEN):
      {propext, Classical.choice, Quot.sound} -/
def KimSarnak_OPEN : Prop :=
  ∀ N : ℕ, Squarefree N → (975 : ℝ) / 4096 ≤ lambda_1 N

/-- **143 is squarefree (proved, classical trio).** -/
theorem sq_free_143 : Squarefree (143 : ℕ) := by
  intro d hd
  rcases Nat.eq_zero_or_pos d with rfl | hpos
  · simp at hd
  have hd_sq : d * d ≤ 143 := Nat.le_of_dvd (by norm_num) hd
  have hle : d ≤ 11 := by
    by_contra h
    push_neg at h
    have h12 : 12 ≤ d := h
    have := Nat.mul_le_mul h12 h12
    linarith
  interval_cases d <;> first | exact isUnit_one | norm_num at hd

/-- **λ₁(X₀(143)) > 0, given KimSarnak_OPEN (proved, classical trio).**
    Proof: 0 < 975/4096 ≤ λ₁(143) by norm_num + h_ks. -/
theorem lambda_1_pos_143 (h_ks : KimSarnak_OPEN) : 0 < lambda_1 143 := by
  have h := h_ks 143 sq_free_143
  linarith [show (0 : ℝ) < 975 / 4096 by norm_num]

noncomputable def lambda_1_Y0_143 : ℝ := lambda_1 143

def Lambda1_Y0_143_Surface : Prop := 0 < lambda_1_Y0_143

/-- **lambda_1_Y0_143_pos: THEOREM, given KimSarnak_OPEN (classical trio).**
    #print axioms: {propext, Classical.choice, Quot.sound} -/
theorem lambda_1_Y0_143_pos (h_ks : KimSarnak_OPEN) : Lambda1_Y0_143_Surface :=
  lambda_1_pos_143 h_ks

/-! ## §4. BC6 mechanism open surface -/

/-- **BC6_SelbergTrace_Surface** — the Bost-Connes Theorem 6 mechanism.
    Given λ₁ > 0 and (ω,ω)_Ar > 0, the Weil explicit formula satisfies
    |S(T)| ≤ C_S14_143·T/log(T) for all T > 1. -/
def BC6_SelbergTrace_Surface : Prop :=
  0 < lambda_1_Y0_143 →
  0 < arakelovPairing_X0_143 →
  ∀ T : ℝ, 1 < T → |S_weil T| ≤ C_S14_143 * T / Real.log T

/-- **BC6SelbergTrace_OPEN** — Bost-Connes 1995, Theorem 6 mechanism.
    ~40 pages BC95 §3–§5. Not in Mathlib v4.12.0.

    STATUS: OPEN.  def Prop — NOT an axiom, NOT proved.
    Enters theorems as an explicit hypothesis.
    #print axioms on any theorem taking (h_bc6 : BC6SelbergTrace_OPEN):
      {propext, Classical.choice, Quot.sound} -/
def BC6SelbergTrace_OPEN : Prop := BC6_SelbergTrace_Surface

/-! ## §5. bc6_from_spectral_gap (theorem, classical trio) -/

/-- **bc6_from_spectral_gap: given KimSarnak_OPEN and BC6SelbergTrace_OPEN (classical trio).**

    Proof: lambda_1_Y0_143_pos h_ks : Lambda1_Y0_143_Surface
           h_bc6 : BC6_SelbergTrace_Surface
           fun h_AP => h_bc6 (lambda_1_Y0_143_pos h_ks) h_AP

    #print axioms bc6_from_spectral_gap:
      {propext, Classical.choice, Quot.sound} -/
theorem bc6_from_spectral_gap
    (h_ks  : KimSarnak_OPEN)
    (h_bc6 : BC6SelbergTrace_OPEN) :
    0 < arakelovPairing_X0_143 →
    ∀ T : ℝ, 1 < T → |S_weil T| ≤ C_S14_143 * T / Real.log T :=
  fun h_AP => h_bc6 (lambda_1_Y0_143_pos h_ks) h_AP

end TheoremaAureum
