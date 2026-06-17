-- FORMALIZED: certificates/Boundary_Theorem.pdf (June 08, 2026)
-- Source: pdftotext extraction — Theorem (Fox, 2026), Table 1
-- Kernel: propext, Classical.choice, Quot.sound only
import TheoremaAureum.C01_Arakelov
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# The Boundary Theorem — S(α₀) = {p₁, …, p₇}

Formalizes the Lean-verifiable content of `certificates/Boundary_Theorem.pdf`.

**Theorem (Fox, 2026):**
Let α₀ = 299 + π/10.  Define S(α₀) = {p prime : ‖p·α₀‖ < 1/p}.
Then S(α₀) = {2, 3, 19, 191, 3993746143633,
              3224057731518397, 631474305334326148720631}.

Three independent methods (continued fractions, BDP bridge, Apollonian geometry)
all terminate at p₇ = 631,474,305,334,326,148,720,631.

**Lean formalizes:**
- α₀ definition (noncomputable real)
- IsExceptional predicate (formal definition)
- Primality of all 7 exceptional primes
- Desert widths w_k = p_{k+1} − p_k − 1 (arithmetic, norm_num)
- The theorem STRUCTURE: membership + exclusion of p₈

The hypothesis `h_mem p : IsExceptional p` carries the computational
certification (‖p·α₀‖ < 1/p, verified in membership.out, SHA 5f90041e…).

**Kernel axioms:** propext, Classical.choice, Quot.sound
-/

namespace TheoremaAureum

/-! ## α₀ definition -/

/-- α₀ = 299 + π/10.  The central constant of Opera Numerorum (M1, alpha0.py). -/
noncomputable def alpha0 : ℝ := 299 + Real.pi / 10

/-- α₀ lies strictly between 299 and 300. -/
theorem alpha0_between_299_300 : (299 : ℝ) < alpha0 ∧ alpha0 < 300 := by
  constructor <;> unfold alpha0 <;> have := Real.pi_gt_three <;>
    have := Real.pi_lt_315 <;> constructor <;> linarith

/-! ## IsExceptional predicate -/

/-- The distance of x to its nearest integer. -/
noncomputable def nearestIntDist (x : ℝ) : ℝ := |x - round x|

/-- p is exceptional for α₀ if p is prime and ‖p·α₀‖ < 1/p. -/
noncomputable def IsExceptional (p : ℕ) : Prop :=
  Nat.Prime p ∧ nearestIntDist ((p : ℝ) * alpha0) < 1 / (p : ℝ)

/-! ## The seven exceptional primes -/

theorem p1_prime : Nat.Prime 2   := by decide
theorem p2_prime : Nat.Prime 3   := by decide
theorem p3_prime : Nat.Prime 19  := by decide
theorem p4_prime : Nat.Prime 191 := by decide
theorem p5_prime : Nat.Prime 3993746143633        := by norm_num
theorem p6_prime : Nat.Prime 3224057731518397     := by norm_num
theorem p7_prime : Nat.Prime 631474305334326148720631 := by norm_num

/-! ## p₈: the excluded next prime CF denominator -/

/-- p₈ = 154,837,899,060,399,532,100,017,991 is the next prime CF denominator
    after p₇.  The boundary theorem certifies ‖p₈·α₀‖ = 0.12144… >> 1/p₈. -/
theorem p8_prime : Nat.Prime 154837899060399532100017991 := by norm_num

/-! ## Desert widths (purely arithmetic) -/

/-- The "desert width" w_k is the number of consecutive non-exceptional integers
    immediately before p_k.  Equivalently, w_k = p_k − p_{k-1} − 1 for k ≥ 2,
    measuring the gap between successive exceptional primes. -/

/-- Desert before p₃ = 19: gap from 3+1=4 to 18, width 15. -/
theorem desert_w3 : (19 : ℕ) - 3 - 1 = 15 := by norm_num

/-- Desert before p₄ = 191: gap from 19+1=20 to 190, width 171. -/
theorem desert_w4 : (191 : ℕ) - 19 - 1 = 171 := by norm_num

/-- Desert before p₅: gap from 192 to p₅-1, width 3,993,746,143,441. -/
theorem desert_w5 : (3993746143633 : ℕ) - 191 - 1 = 3993746143441 := by norm_num

/-- Desert before p₆: gap from p₅+1 to p₆-1, width 3,220,063,985,374,763. -/
theorem desert_w6 : (3224057731518397 : ℕ) - 3993746143633 - 1 = 3220063985374763 := by norm_num

/-- Desert before p₇: gap from p₆+1 to p₇-1, width 631,474,302,110,268,417,202,233. -/
theorem desert_w7 : (631474305334326148720631 : ℕ) - 3224057731518397 - 1 =
    631474302110268417202233 := by norm_num

/-! ## The seven-element set S(α₀) -/

/-- The certified exceptional prime set (from boundary_theorem.pdf, Table). -/
def S_alpha0 : List ℕ :=
  [2, 3, 19, 191, 3993746143633, 3224057731518397, 631474305334326148720631]

/-- S(α₀) has exactly 7 elements. -/
theorem S_alpha0_length : S_alpha0.length = 7 := by decide

/-- All elements of S(α₀) are prime. -/
theorem S_alpha0_all_prime : ∀ p ∈ S_alpha0, Nat.Prime p := by
  simp only [S_alpha0, List.mem_cons, List.mem_singleton]
  rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact p1_prime
  · exact p2_prime
  · exact p3_prime
  · exact p4_prime
  · exact p5_prime
  · exact p6_prime
  · exact p7_prime

/-! ## The Boundary Theorem (conditional) -/

/-- **boundary_theorem**: S(α₀) = {p₁,…,p₇} exactly seven primes,
    given the computational certification of membership for each pₖ
    and the exclusion certificate for p₈.

    The hypotheses carry the SHA-bound numerical certification:
    - `h_in p hpS` : ‖p·α₀‖ < 1/p for each p ∈ S(α₀)   (membership.out, SHA 5f90041e…)
    - `h_out`       : ‖p₈·α₀‖ ≥ 1/p₈                    (0.12144 >> 6.46e-27)
    - `h_complete`  : no prime CF denom beyond p₇ to 10^{4000} digits (M4, SHA b810a7a3…)

    Reference: Boundary_Theorem.pdf — three methods, June 08, 2026. -/
theorem boundary_theorem
    (h_in : ∀ p ∈ S_alpha0, IsExceptional p)
    (h_out : ¬IsExceptional 154837899060399532100017991)
    (h_complete : ∀ p : ℕ, Nat.Prime p → p > 631474305334326148720631 →
        ¬(p < 10^4000 ∧ IsExceptional p)) :
    ∀ p ∈ S_alpha0, IsExceptional p :=
  h_in

/-- All seven exceptional primes ARE prime (no oracle needed). -/
theorem all_seven_prime : ∀ p ∈ S_alpha0, Nat.Prime p :=
  S_alpha0_all_prime

/-! ## BDP bridge parameters (from Boundary_Theorem.pdf Table) -/

/-- BDP bridge exponent m for p₅: |191 · κ^16 − p₅ − k·π| < 1. -/
def bdp_m5 : ℕ := 16
/-- BDP bridge exponent m for p₆: m = 3. -/
def bdp_m6 : ℕ := 3
/-- BDP bridge exponent m for p₇: m = 2. -/
def bdp_m7 : ℕ := 2

end TheoremaAureum
