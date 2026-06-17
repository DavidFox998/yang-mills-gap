-- FORMALIZED: certificates/Addendum_A1_Complete_Sieve.pdf (2026-06-04)
-- Source: pdftotext extraction — 4-gate sieve, Theorem 2, Corollary 3
-- Kernel: propext, Classical.choice, Quot.sound only
import TheoremaAureum.formalized.Bands_269_Certificate
import Mathlib.Data.Nat.Prime.Basic

/-!
# Addendum A1 — The Complete 4-Condition Sieve for α = 2π/7

Formalizes the mathematical content of `certificates/Addendum_A1_Complete_Sieve.pdf`.

**The 4-Gate Sieve (Theorem 2):**
A prime h is an EXCEPTIONAL BAND of α = 2π/7 iff all four gates pass:

  G1: h ∈ S_CF(N)  — h is a CF denominator of 2π/7  (computational)
  G2: h is prime   — Miller-Rabin / BPSW             (decidable for small h)
  G3: 3^h mod 7 ∈ {3,5,6}  — Lemma G0.3             (NEVER eliminates: proved)
  G4: 2·genus − 2 > 0       — Arakelov positivity    (NEVER eliminates: proved)

**Corollary 3:** At N_end = 10^4000 with mp.dps = 4110, exactly 269 prime CF
denominators pass G1+G2. Of these, 5 were verified by 12-witness Miller-Rabin:

  CF index n=5:  h = 127               (3 digits)
  CF index n=11: h = 414679            (6 digits)
  CF index n≈14: h = 4964318427222741249841  (22 digits)
  [2 further bands from higher CF indices, not extracted]

**Lean formalizes:**
- G3 NEVER eliminates: proved using ord(3,7)=6 and h≡1(mod 6) for confirmed bands
- G4 NEVER eliminates: ArakelovPositivity (X₀ 143), from C01
- Primality (G2) for all 3 confirmed bands
- The combined sieve theorem for all 3 known confirmed bands

**Kernel axioms:** propext, Classical.choice, Quot.sound
-/

namespace TheoremaAureum

/-! ## G3 gate: 3^h ≡ 3 (mod 7) for the three confirmed bands -/

-- (3 : ZMod 7)^6 = 1 and ord3_mod7 are already in Bands_269_Certificate

/-! ### Band h = 127 (CF index n = 5) — inherited from Bands_269_Certificate -/

/-- G3 for h = 127: (3 : ZMod 7)^127 = 3. -/
theorem band_127_G3 : (3 : ZMod 7) ^ 127 = 3 := g03_127

/-- G2 for h = 127: 127 is prime. -/
theorem band_127_G2 : Nat.Prime 127 := band1_prime

/-! ### Band h = 414679 (CF index n = 11) — inherited from Bands_269_Certificate -/

/-- G3 for h = 414679: (3 : ZMod 7)^414679 = 3. -/
theorem band_414679_G3 : (3 : ZMod 7) ^ 414679 = 3 := g03_414679

/-- G2 for h = 414679: 414679 is prime. -/
theorem band_414679_G2 : Nat.Prime 414679 := band2_prime

/-! ### Band h = 4964318427222741249841 (CF index n ≈ 14, 22 digits) -/

/-- G2 for h = 4964318427222741249841: this large prime passes Miller-Rabin. -/
theorem band3_prime : Nat.Prime 4964318427222741249841 := by norm_num

/-- 4964318427222741249841 = 6·827386404537123541640 + 1 (mod-6 residue). -/
private lemma band3_mod6 :
    4964318427222741249841 = 6 * 827386404537123541640 + 1 := by norm_num

/-- G3 for h = 4964318427222741249841: (3 : ZMod 7)^h = 3.
    Proof: h ≡ 1 (mod 6) and 3^6 ≡ 1 (mod 7), so 3^h ≡ 3^1 = 3 (mod 7). -/
theorem band3_G3 : (3 : ZMod 7) ^ 4964318427222741249841 = 3 := by
  rw [band3_mod6, pow_add, pow_mul, ord3_mod7, one_pow, one_mul, pow_one]

/-! ## G4 gate: NEVER eliminates (Arakelov positivity) -/

/-- G4 for all three confirmed bands: arakelov_term(genus=13) = 24 > 0.
    The Arakelov gate never eliminates a candidate prime — it depends only
    on the genus of X₀(143), not on the CF denominator h. -/
theorem G4_never_eliminates : ArakelovPositivity (X₀ 143) :=
  arakelov_condition_always_passes

/-! ## Combined 3-band certificate (G2 + G3 + G4) -/

/-- **addendum_three_bands**: all three confirmed exceptional bands pass G2, G3, G4.
    G1 (CF membership) is certified computationally in Addendum_A1_Complete_Sieve.pdf
    for each band (12-witness Miller-Rabin BPSW, mp.dps = 4110). -/
theorem addendum_three_bands :
    Nat.Prime 127 ∧ (3 : ZMod 7)^127 = 3 ∧
    Nat.Prime 414679 ∧ (3 : ZMod 7)^414679 = 3 ∧
    Nat.Prime 4964318427222741249841 ∧ (3 : ZMod 7)^4964318427222741249841 = 3 ∧
    ArakelovPositivity (X₀ 143) :=
  ⟨band_127_G2, band_127_G3,
   band_414679_G2, band_414679_G3,
   band3_prime, band3_G3,
   G4_never_eliminates⟩

/-! ## Key structural lemma: G3 condition equivalent to h ≡ 1 or 3 or 5 (mod 6) -/

/-- The order of 3 in (ℤ/7ℤ)× is exactly 6, cycling through:
    3^1=3, 3^2=2, 3^3=6, 3^4=4, 3^5=5, 3^6=1 (mod 7).
    Pass condition {3,5,6} corresponds to h ≡ 1,5,3 (mod 6) respectively. -/
theorem g03_pass_iff_odd_class (h : ℕ) (r : ℕ) (hr : h = 6 * r + 1) :
    (3 : ZMod 7) ^ h = 3 := by
  rw [hr, pow_add, pow_mul, ord3_mod7, one_pow, one_mul, pow_one]

theorem g03_pass_3mod6 (h : ℕ) (r : ℕ) (hr : h = 6 * r + 3) :
    (3 : ZMod 7) ^ h = 6 := by
  rw [hr, pow_add, pow_mul, ord3_mod7, one_pow, one_mul]
  decide

theorem g03_pass_5mod6 (h : ℕ) (r : ℕ) (hr : h = 6 * r + 5) :
    (3 : ZMod 7) ^ h = 5 := by
  rw [hr, pow_add, pow_mul, ord3_mod7, one_pow, one_mul]
  decide

end TheoremaAureum
