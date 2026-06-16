-- SU(3) instance stack for haarMeasure
-- Towers/YM/SU3Instances.lean
-- Equips specialUnitaryGroup (Fin 3) ℂ with the instance stack required for
-- MeasureTheory.Measure.haarMeasure ⊤ to elaborate.
-- Axioms: {propext, Classical.choice, Quot.sound}  SORRY: 0
-- NOT a mass-gap proof; Surface #1 stays OPEN.

import Mathlib

open MeasureTheory Matrix

namespace TheoremaAureum.SU3

set_option linter.dupNamespace false in
abbrev SU3 := Matrix.specialUnitaryGroup (Fin 3) ℂ

-- =========================================================================
-- Group structure
-- SU3 is a Submonoid of Matrix.  We add an inverse (= star/conjugate-
-- transpose) using the same pattern as Group (unitary R) in
-- Mathlib/Algebra/Star/Unitary.lean (line 89).
-- =========================================================================

private lemma su3_star_mem {A : Matrix (Fin 3) (Fin 3) ℂ}
    (hA : A ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ) :
    star A ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff] at hA ⊢
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · rw [star_star]; exact Matrix.mem_unitaryGroup_iff'.mp hA.1
  · -- det(A * star A) = det(1) = 1; expand via det_mul and use det A = 1.
    have hmul' : A * star A = 1 := Matrix.mem_unitaryGroup_iff.mp hA.1
    have hd := congr_arg Matrix.det hmul'
    simp only [Matrix.det_mul, Matrix.det_one] at hd
    rw [hA.2, one_mul] at hd
    exact hd

instance : Group SU3 :=
  { Submonoid.toMonoid _ with
    inv := fun A => ⟨star A.val, su3_star_mem A.prop⟩
    inv_mul_cancel := fun A => Subtype.ext (by
      show star A.val * A.val = 1
      exact Matrix.mem_unitaryGroup_iff'.mp
            (Matrix.mem_specialUnitaryGroup_iff.mp A.prop).1) }

-- =========================================================================
-- Topological group structure
-- ContinuousMul is automatic via Submonoid.continuousMul.
-- We add ContinuousInv: the map A ↦ star A.val is continuous.
-- =========================================================================

instance : ContinuousInv SU3 := ⟨
  Continuous.subtype_mk
    (continuous_star.comp continuous_subtype_val)
    (fun A => su3_star_mem A.prop)⟩

instance : TopologicalGroup SU3 where
  continuous_mul := continuous_mul
  continuous_inv := continuous_inv

-- =========================================================================
-- Compact space
-- Strategy: carrier of SU3 ⊆ poly-disc (entries ≤ 1 by unitarity) and
-- is closed (A * Aᴴ = 1 and det A = 1 are preimages of {1} under
-- continuous maps).
-- =========================================================================

private lemma entry_norm_bound_of_unitary
    {A : Matrix (Fin 3) (Fin 3) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin 3) ℂ) (i j : Fin 3) : ‖A i j‖ ≤ 1 := by
  have hmul : A * star A = 1 := Matrix.mem_unitaryGroup_iff.mp hA
  have hii : ∑ k : Fin 3, A i k * (star A) k i = 1 := by
    have h1 : (A * star A) i i = 1 := by rw [hmul]; simp
    simp only [Matrix.mul_apply] at h1
    exact h1
  have hterm : ∀ k : Fin 3, A i k * (star A) k i = ↑(Complex.normSq (A i k)) := fun k => by
    rw [Matrix.star_apply]
    exact Complex.mul_conj (A i k)
  have hrow : ∑ k : Fin 3, Complex.normSq (A i k) = 1 := by
    have heq : ∀ k : Fin 3, (Complex.normSq (A i k) : ℂ) = A i k * (star A) k i :=
      fun k => (hterm k).symm
    have hsum : (∑ k : Fin 3, (Complex.normSq (A i k) : ℂ)) = 1 := by
      simp_rw [heq]; exact hii
    have hre := congr_arg Complex.re hsum
    simp only [map_sum, Complex.ofReal_re, Complex.one_re] at hre
    exact hre
  have hle : Complex.normSq (A i j) ≤ 1 :=
    hrow ▸ Finset.single_le_sum
      (fun k _ => Complex.normSq_nonneg (A i k)) (Finset.mem_univ j)
  have hsq : ‖A i j‖ ^ 2 ≤ 1 := by
    rw [Complex.norm_eq_abs, Complex.sq_abs]; exact hle
  nlinarith [norm_nonneg (A i j)]

private lemma su3_carrier_isCompact :
    IsCompact (Set.range (Subtype.val : SU3 → Matrix (Fin 3) (Fin 3) ℂ)) := by
  apply IsCompact.of_isClosed_subset
    (isCompact_univ_pi (fun _ : Fin 3 =>
      isCompact_univ_pi (fun _ : Fin 3 => isCompact_closedBall (0 : ℂ) 1)))
  · have hset : Set.range (Subtype.val : SU3 → Matrix (Fin 3) (Fin 3) ℂ) =
        {A | A * star A = 1} ∩ {A | Matrix.det A = 1} := by
      ext A
      constructor
      · rintro ⟨⟨A', hA'⟩, rfl⟩
        exact ⟨Matrix.mem_unitaryGroup_iff.mp
                 (Matrix.mem_specialUnitaryGroup_iff.mp hA').1,
               (Matrix.mem_specialUnitaryGroup_iff.mp hA').2⟩
      · intro ⟨h1, h2⟩
        exact ⟨⟨A, Matrix.mem_specialUnitaryGroup_iff.mpr
                 ⟨Matrix.mem_unitaryGroup_iff.mpr h1, h2⟩⟩, rfl⟩
    rw [hset]
    exact (isClosed_eq (continuous_id.mul continuous_star) continuous_const).inter
          (isClosed_eq (Continuous.matrix_det continuous_id) continuous_const)
  · rintro A ⟨⟨A', hA'⟩, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left,
               Metric.mem_closedBall, dist_zero_right]
    exact fun i j => entry_norm_bound_of_unitary
      (Matrix.mem_specialUnitaryGroup_iff.mp hA').1 i j

instance : CompactSpace SU3 := by
  constructor
  rw [Subtype.isCompact_iff, Set.image_univ]
  exact su3_carrier_isCompact

-- =========================================================================
-- Measurable / Borel structure  (inherited as a metric subspace)
--
-- Lean4 v4.12.0 cannot always unfold the Matrix abbrev (m → n → α) during
-- typeclass synthesis for MeasurableSpace.  We thread the instances by
-- naming them explicitly:
--   su3_mat_meas  : MeasurableSpace (Matrix (Fin 3) (Fin 3) ℂ)
--   su3_mat_borel : BorelSpace      (Matrix (Fin 3) (Fin 3) ℂ)
-- then derive MeasurableSpace ↥SU3 / BorelSpace ↥SU3 via Subtype lemmas.
-- =========================================================================

-- Matrix (Fin 3) (Fin 3) ℂ is an abbrev for Fin 3 → Fin 3 → ℂ; Lean4 instance
-- synthesis won't see through the abbrev automatically. Use `change` to expose the Pi type.
private instance su3_mat_meas : MeasurableSpace (Matrix (Fin 3) (Fin 3) ℂ) := by
  change MeasurableSpace (Fin 3 → Fin 3 → ℂ)
  infer_instance

-- Same abbrev issue: change to Pi type so Lean4 can apply Pi.borelSpace freely.
private instance su3_mat_borel : BorelSpace (Matrix (Fin 3) (Fin 3) ℂ) := by
  change BorelSpace (Fin 3 → Fin 3 → ℂ)
  infer_instance

instance : MeasurableSpace ↥SU3 := Subtype.instMeasurableSpace

-- Use Subtype.borelSpace _ (inferred set = ↑SU3) rather than SU3.carrier
-- to avoid a CoeSort mismatch (↑SU3.carrier ≠ ↥SU3 as types).
instance : BorelSpace ↥SU3 := Subtype.borelSpace _

-- =========================================================================
-- Haar measure on SU(3)
-- =========================================================================

noncomputable def haarSU3 : Measure SU3 :=
  MeasureTheory.Measure.haarMeasure ⊤

end TheoremaAureum.SU3
