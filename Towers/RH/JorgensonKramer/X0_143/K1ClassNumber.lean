/-
  Towers/RH/JorgensonKramer/X0_143/K1ClassNumber.lean

  Class number certificate for K = ℚ(√-143).

  FULLY PROVED IN THIS FILE (sorry = 0, axiom footprint = classical trio):
    nrRealPlaces_zero       NrRealPlaces K = 0        (α² = -143 has no real root)
    nrComplexPlaces_one     NrComplexPlaces K = 1     (card_add_two_mul_card_eq_rank)
    minkowski_lt_eight      (2/π)·√143 < 8            (numeric; π > 3, √143 < 12)
    norm_form_no_norm_2k    no a b : ℤ with norm 2^k  (for k = 1,3,5,7,9)

  OPEN SURFACES (def Prop — not sorry, not axiom, taken as explicit hyp):
    K1_ClassNumber_Upper_OPEN   classNumber K ≤ 10
    K1_ClassNumber_Lower_OPEN   10 ≤ classNumber K
    K1_ClassNumber_Certificate  classNumber K = 10  (closes K1_ClassNumber_OPEN)

  Proof route for K1_ClassNumber_Certificate (sketched, requires future session):
    Upper bound: every ideal class has representative of norm ≤ 7 (Minkowski);
      primes ≤ 7 give ≤ 10 generators in the class group.
    Lower bound: 𝔭₂ = Ideal.span {2, ω_int} has order 10 in ClassGroup(𝓞 K);
      generator of 𝔭₂^10: x = -28·1 + 3·ω_int, norm = 784 - 84 + 324 = 1024 = 2^10;
      𝔭₂^k non-principal for k=1..9 (norm form has no solution for odd k, and
      for even k the only norm-2^k elements are ±2^(k/2) which generate 𝔭₂^(k/2)·𝔭₂'^(k/2)).

  SORRY: 0.  AXIOM FOOTPRINT: classical trio {propext, Classical.choice, Quot.sound}.
-/
import Mathlib.NumberTheory.NumberField.Discriminant
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.RingTheory.ClassGroup
import Towers.RH.JorgensonKramer.X0_143.Discriminant143

namespace Towers.RH.JorgensonKramer.X0_143

open Polynomial NumberField NumberField.ComplexEmbedding NumberField.InfinitePlace
open Real FiniteDimensional

/-! ### Step 1: No real embeddings ⟹ NrRealPlaces K = 0 -/

private lemma no_real_embedding (φ : K →+* ℂ) : ¬ IsReal φ := by
  intro hreal
  -- Use the real embedding hreal.embedding : K →+* ℝ directly
  have hα : hreal.embedding α ^ 2 = -(143 : ℝ) := by
    have h := congr_arg hreal.embedding α_sq
    simp [map_pow, map_neg, map_natCast] at h
    exact h
  linarith [sq_nonneg (hreal.embedding α), hα]

/-- PROVED: NrRealPlaces K = 0. -/
theorem nrRealPlaces_zero : NrRealPlaces K = 0 := by
  -- NrRealPlaces K unfolds to Fintype.card { w // w.IsReal } which is transparent
  simp only [Fintype.card_eq_zero_iff, isEmpty_subtype]
  intro w hw
  exact no_real_embedding w.embedding hw

/-! ### Step 2: NrComplexPlaces K = 1 -/

/-- PROVED: NrComplexPlaces K = 1. -/
theorem nrComplexPlaces_one : NrComplexPlaces K = 1 := by
  have h := card_add_two_mul_card_eq_rank K
  rw [nrRealPlaces_zero, finrank_K_Q] at h
  omega

/-! ### Step 3: Minkowski bound -/

private lemma sqrt_143_lt_twelve : Real.sqrt 143 < 12 := by
  have h : Real.sqrt 143 < Real.sqrt 144 := by
    apply Real.sqrt_lt_sqrt <;> norm_num
  have h12 : Real.sqrt 144 = 12 := by
    rw [show (144 : ℝ) = 12 ^ 2 from by norm_num]
    exact Real.sqrt_sq (by norm_num)
  linarith

/-- PROVED: (2/π)·√143 < 8. -/
theorem minkowski_lt_eight : 2 / Real.pi * Real.sqrt 143 < 8 := by
  have hπ_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h1 : Real.sqrt 143 < 12 := sqrt_143_lt_twelve
  have h2 : 2 / Real.pi * Real.sqrt 143 < 2 / Real.pi * 12 := by
    apply mul_lt_mul_of_pos_left h1
    exact div_pos (by norm_num) hπ_pos
  have h3 : 2 / Real.pi * 12 < 8 := by
    rw [div_mul_eq_mul_div, div_lt_iff hπ_pos]
    linarith
  linarith

/-! ### Step 4: Norm form impossibility for 2^k, odd k -/

private lemma one_le_sq_of_ne_zero {n : ℤ} (hn : n ≠ 0) : 1 ≤ n ^ 2 := by
  rcases lt_or_gt_of_ne hn with h | h
  · have hle : n ≤ -1 := Int.le_sub_one_of_lt h
    nlinarith [sq_nonneg (n + 1)]
  · nlinarith [sq_nonneg (n - 1)]

/-- No a b : ℤ satisfy a² + ab + 36b² = 2. -/
lemma norm_form_no_norm_two (a b : ℤ) : a ^ 2 + a * b + 36 * b ^ 2 ≠ 2 := by
  intro h
  have heq : (2 * a + b) ^ 2 + 143 * b ^ 2 = 8 := by linear_combination 4 * h
  have hb : b = 0 := by
    by_contra hb'
    nlinarith [one_le_sq_of_ne_zero hb', sq_nonneg (2 * a + b)]
  subst hb; simp only [mul_zero, add_zero] at h
  have ha_le : a ≤ 1 := by nlinarith [sq_nonneg (a - 1)]
  have ha_ge : -1 ≤ a := by nlinarith [sq_nonneg (a + 1)]
  interval_cases a <;> simp_all

/-- No a b : ℤ satisfy a² + ab + 36b² = 8. -/
lemma norm_form_no_norm_eight (a b : ℤ) : a ^ 2 + a * b + 36 * b ^ 2 ≠ 8 := by
  intro h
  have heq : (2 * a + b) ^ 2 + 143 * b ^ 2 = 32 := by linear_combination 4 * h
  have hb : b = 0 := by
    by_contra hb'
    nlinarith [one_le_sq_of_ne_zero hb', sq_nonneg (2 * a + b)]
  subst hb; simp only [mul_zero, add_zero] at h
  have ha_le : a ≤ 2 := by nlinarith [sq_nonneg (a - 3)]
  have ha_ge : -2 ≤ a := by nlinarith [sq_nonneg (a + 3)]
  interval_cases a <;> simp_all

/-- No a b : ℤ satisfy a² + ab + 36b² = 32. -/
lemma norm_form_no_norm_32 (a b : ℤ) : a ^ 2 + a * b + 36 * b ^ 2 ≠ 32 := by
  intro h
  have heq : (2 * a + b) ^ 2 + 143 * b ^ 2 = 128 := by linear_combination 4 * h
  have hb : b = 0 := by
    by_contra hb'
    nlinarith [one_le_sq_of_ne_zero hb', sq_nonneg (2 * a + b)]
  subst hb; simp only [mul_zero, add_zero] at h
  have ha_le : a ≤ 5 := by nlinarith [sq_nonneg (a - 6)]
  have ha_ge : -5 ≤ a := by nlinarith [sq_nonneg (a + 6)]
  interval_cases a <;> simp_all

/-- No a b : ℤ satisfy a² + ab + 36b² = 128. -/
lemma norm_form_no_norm_128 (a b : ℤ) : a ^ 2 + a * b + 36 * b ^ 2 ≠ 128 := by
  intro h
  have heq : (2 * a + b) ^ 2 + 143 * b ^ 2 = 512 := by linear_combination 4 * h
  have hb1 : b ^ 2 ≤ 3 := by nlinarith [sq_nonneg (2 * a + b)]
  have hble : b ≤ 1 := by nlinarith [sq_nonneg (b - 2)]
  have hbge : -1 ≤ b := by nlinarith [sq_nonneg (b + 2)]
  interval_cases b
  · simp only [mul_zero, add_zero] at h
    have ha_le : a ≤ 11 := by nlinarith [sq_nonneg (a - 12)]
    have ha_ge : -11 ≤ a := by nlinarith [sq_nonneg (a + 12)]
    interval_cases a <;> simp_all
  · ring_nf at h
    have h' : a ^ 2 + a - 92 = 0 := by linarith
    have ha_le : a ≤ 9 := by nlinarith [sq_nonneg (a - 10)]
    have ha_ge : -10 ≤ a := by nlinarith [sq_nonneg (a + 10)]
    interval_cases a <;> omega
  · ring_nf at h
    have h' : a ^ 2 - a - 92 = 0 := by linarith
    have ha_le : a ≤ 10 := by nlinarith [sq_nonneg (a - 10)]
    have ha_ge : -9 ≤ a := by nlinarith [sq_nonneg (a + 10)]
    interval_cases a <;> omega

/-- No a b : ℤ satisfy a² + ab + 36b² = 512. -/
lemma norm_form_no_norm_512 (a b : ℤ) : a ^ 2 + a * b + 36 * b ^ 2 ≠ 512 := by
  intro h
  have heq : (2 * a + b) ^ 2 + 143 * b ^ 2 = 2048 := by linear_combination 4 * h
  have hb2 : b ^ 2 ≤ 14 := by nlinarith [sq_nonneg (2 * a + b)]
  have hble : b ≤ 3 := by nlinarith [sq_nonneg (b - 4)]
  have hbge : -3 ≤ b := by nlinarith [sq_nonneg (b + 4)]
  interval_cases b
  · have h' : a ^ 2 - 3 * a - 188 = 0 := by linarith
    have ha_le : a ≤ 16 := by nlinarith [sq_nonneg (a - 17)]
    have ha_ge : -13 ≤ a := by nlinarith [sq_nonneg (a + 14)]
    interval_cases a <;> omega
  · have h' : a ^ 2 - 2 * a - 368 = 0 := by linarith
    have ha_le : a ≤ 20 := by nlinarith [sq_nonneg (a - 21)]
    have ha_ge : -18 ≤ a := by nlinarith [sq_nonneg (a + 19)]
    interval_cases a <;> omega
  · have h' : a ^ 2 - a - 476 = 0 := by linarith
    have ha_le : a ≤ 22 := by nlinarith [sq_nonneg (a - 23)]
    have ha_ge : -21 ≤ a := by nlinarith [sq_nonneg (a + 22)]
    interval_cases a <;> omega
  · simp only [mul_zero, add_zero] at h
    have ha_le : a ≤ 22 := by nlinarith [sq_nonneg (a - 23)]
    have ha_ge : -22 ≤ a := by nlinarith [sq_nonneg (a + 23)]
    interval_cases a <;> simp_all
  · have h' : a ^ 2 + a - 476 = 0 := by linarith
    have ha_le : a ≤ 21 := by nlinarith [sq_nonneg (a - 22)]
    have ha_ge : -22 ≤ a := by nlinarith [sq_nonneg (a + 22)]
    interval_cases a <;> omega
  · have h' : a ^ 2 + 2 * a - 368 = 0 := by linarith
    have ha_le : a ≤ 18 := by nlinarith [sq_nonneg (a - 19)]
    have ha_ge : -20 ≤ a := by nlinarith [sq_nonneg (a + 20)]
    interval_cases a <;> omega
  · have h' : a ^ 2 + 3 * a - 188 = 0 := by linarith
    have ha_le : a ≤ 13 := by nlinarith [sq_nonneg (a - 14)]
    have ha_ge : -16 ≤ a := by nlinarith [sq_nonneg (a + 16)]
    interval_cases a <;> omega

/-! ### Step 5: Open surfaces toward classNumber K = 10 -/

/-- K1_ClassNumber_Upper_OPEN: h(K) ≤ 10.
    Uses Fintype.card (ClassGroup (𝓞 K)) as the class number.
    STATUS: OPEN. Do NOT discharge with sorry/native_decide/trivial. -/
def K1_ClassNumber_Upper_OPEN : Prop := Fintype.card (ClassGroup (𝓞 K)) ≤ 10

/-- K1_ClassNumber_Lower_OPEN: 10 ≤ h(K).
    STATUS: OPEN. Do NOT discharge with sorry/native_decide/trivial. -/
def K1_ClassNumber_Lower_OPEN : Prop := 10 ≤ Fintype.card (ClassGroup (𝓞 K))

/-- K1_ClassNumber_Certificate: h(K) = 10.
    COMBINATOR (0 sorry, classical trio only): given the two open surfaces as
    explicit hypotheses, the equality is immediate. -/
theorem K1_ClassNumber_Certificate
    (h_upper : K1_ClassNumber_Upper_OPEN)
    (h_lower : K1_ClassNumber_Lower_OPEN) :
    Fintype.card (ClassGroup (𝓞 K)) = 10 :=
  Nat.le_antisymm h_upper h_lower

end Towers.RH.JorgensonKramer.X0_143
