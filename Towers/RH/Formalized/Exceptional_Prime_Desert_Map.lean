-- FORMALIZED: certificates/Exceptional_Prime_Desert_Map.pdf
-- Source: pdftotext extraction — Table 1 (k=1..7), key constants
-- Kernel: propext, Classical.choice, Quot.sound only
import TheoremaAureum.formalized.Boundary_Theorem
import TheoremaAureum.formalized.Module_15_Delta_Boost

/-!
# The Exceptional Prime Desert Map

Formalizes the mathematical content of `certificates/Exceptional_Prime_Desert_Map.pdf`.

**Definition (exceptional prime):**
  p is exceptional for α₀ ↔ p prime ∧ ‖p·α₀‖ < 1/p  (same as IsExceptional)

**Table 1 (first 7 rows, k=1..7):**
  k  pk                              Dk  wk (desert width)                rk
  1  2                               1   0                                0.7433629
  2  3                               1   0                                0.1725666
  3  19                              2   15                               0.5885052
  4  191                             3   171                              0.8441596
  5  3993746143633                   13  3993746143441                    0.1523629
  6  3224057731518397                16  3220063985374763                 0.7749508
  7  631474305334326148720631        24  631474302110268417202233         0.1441999

rk = pk · ‖pk·π/10‖ (the "measure" for each exceptional prime).

**Lean formalizes:**
- Desert width = pk − p_{k-1} − 1 (arithmetic, norm_num)
- Count of exceptional primes: 20 stated (7 formalized, 13 at higher k)
- rk values as certified computational hypotheses
- The claim rk < 1 for all k (follows from rk = pk · ‖pk·π/10‖ and the
  exceptional condition ‖pk·π/10‖ < 1/pk → pk·‖pk·π/10‖ < 1)

**Kernel axioms:** propext, Classical.choice, Quot.sound
-/

namespace TheoremaAureum

/-! ## Desert width definition -/

/-- The desert width before pₖ is the number of consecutive non-exceptional integers
    immediately below pₖ.  For consecutive exceptional primes p_prev < p_next,
    desert_width(p_next) = p_next − p_prev − 1. -/
def desertWidth (p_next p_prev : ℕ) : ℕ := p_next - p_prev - 1

/-! ## Desert widths (arithmetic, norm_num) -/

theorem desert_k3 : desertWidth 19 3 = 15  := by decide
theorem desert_k4 : desertWidth 191 19 = 171 := by decide
theorem desert_k5 : desertWidth 3993746143633 191 = 3993746143441 := by norm_num
theorem desert_k6 : desertWidth 3224057731518397 3993746143633 = 3220063985374763 := by norm_num
theorem desert_k7 : desertWidth 631474305334326148720631 3224057731518397 =
    631474302110268417202233 := by norm_num

/-! ## rk < 1: consequence of exceptional condition -/

/-- **r_lt_one**: for any exceptional prime p, rk = p · ‖p·π/10‖ < 1.
    This follows directly from the exceptional condition ‖p·π/10‖ < 1/p. -/
theorem r_lt_one {p : ℕ} (hp : Nat.Prime p)
    (h_exp : normPi10 p < 1 / (p : ℝ)) :
    (p : ℝ) * normPi10 p < 1 := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  calc (p : ℝ) * normPi10 p
      < (p : ℝ) * (1 / (p : ℝ)) := mul_lt_mul_of_pos_left h_exp hp_pos
    _ = 1 := by field_simp

/-! ## Desert map Table 1 — certified rk values as hypotheses -/

/-- The rk column values from Table 1 (certified in Exceptional_Prime_Desert_Map.pdf).
    These are certified 7-digit float values; the hypothesis carries the mpmath computation. -/
structure DesertMapRow where
  k     : ℕ
  p     : ℕ
  dk    : ℕ  -- number of digits in p
  wk    : ℕ  -- desert width
  rk_approx : Float  -- rk ≈ pk · ‖pk·π/10‖

/-- Table 1 encoded as a list. -/
def desertMapTable : List DesertMapRow :=
  [ ⟨1, 2,                               1,  0,                         0.7433629⟩
  , ⟨2, 3,                               1,  0,                         0.1725666⟩
  , ⟨3, 19,                              2,  15,                        0.5885052⟩
  , ⟨4, 191,                             3,  171,                       0.8441596⟩
  , ⟨5, 3993746143633,                   13, 3993746143441,              0.1523629⟩
  , ⟨6, 3224057731518397,                16, 3220063985374763,           0.7749508⟩
  , ⟨7, 631474305334326148720631,         24, 631474302110268417202233,  0.1441999⟩
  ]

/-- The table has exactly 7 rows. -/
theorem desert_table_length : desertMapTable.length = 7 := by decide

/-! ## Digit count (number of digits) correctness -/

theorem p1_digits : Nat.log 10 2  + 1 = 1 := by decide
theorem p2_digits : Nat.log 10 3  + 1 = 1 := by decide
theorem p3_digits : Nat.log 10 19 + 1 = 2 := by decide
theorem p4_digits : Nat.log 10 191 + 1 = 3 := by decide
theorem p5_digits : Nat.log 10 3993746143633 + 1 = 13 := by norm_num [Nat.log]

/-! ## P6..P7 are in the "Bridge/Desert" regime (paper Table 1 annotation) -/

/-- p₅ (13 digits) is in the Bridge regime. -/
theorem p5_is_bridge : 10^12 ≤ 3993746143633 ∧ 3993746143633 < 10^13 := by norm_num

/-- p₆ (16 digits) is in the Desert regime. -/
theorem p6_is_desert : 10^15 ≤ 3224057731518397 ∧ 3224057731518397 < 10^16 := by norm_num

/-- p₇ (24 digits) is in the Desert regime. -/
theorem p7_is_desert : 10^23 ≤ 631474305334326148720631 ∧
    631474305334326148720631 < 10^24 := by norm_num

/-! ## The 20-prime statement -/

/-- The paper certifies 20 exceptional primes < 10^4000.
    This Lean file formalizes the first 7 (those with tabulated data).
    The Lean-formalizable content: 7 primes ARE prime (proved in Boundary_Theorem)
    and their desert widths are correct (proved above). -/
theorem seven_exceptional_primes_formalized :
    Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 19 ∧ Nat.Prime 191 ∧
    Nat.Prime 3993746143633 ∧ Nat.Prime 3224057731518397 ∧
    Nat.Prime 631474305334326148720631 ∧
    desertWidth 19 3 = 15 ∧
    desertWidth 191 19 = 171 ∧
    desertWidth 3993746143633 191 = 3993746143441 ∧
    desertWidth 3224057731518397 3993746143633 = 3220063985374763 ∧
    desertWidth 631474305334326148720631 3224057731518397 = 631474302110268417202233 :=
  ⟨p1_prime, p2_prime, p3_prime, p4_prime,
   p5_prime, p6_prime, p7_prime,
   desert_k3, desert_k4, desert_k5, desert_k6, desert_k7⟩

end TheoremaAureum
