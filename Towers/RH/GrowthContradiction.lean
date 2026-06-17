/-
  # Towers.RH.GrowthContradiction

  **This file does NOT prove the Riemann Hypothesis.** It records, as an
  *honest conditional reduction*, the argument sketched in David Fox's
  fragment "Hr sec 4 phone":

      Lemma (Growth bound).  ∃ C > 0, ∀ t ≥ 2, |ζ(½+it)| ≤ C (log t)².
      Theorem (RH).          every nontrivial zero ρ has Re ρ = ½.
      Proof.                 an off-line zero forces, "by standard
                             zero-repulsion", |ζ(½+it)| ≥ exp(c₁ log t / log log t)
                             for arbitrarily large t, contradicting the Lemma.

  ## Why the paper does NOT prove RH (honest assessment)

  The argument is recreated faithfully below as the combinator
  `riemannHypothesis_of_growth_and_repulsion`, whose entire RH-content sits in
  TWO named hypotheses that are **never discharged**:

  * `GrowthBound` — the paper's growth Lemma. This is *far stronger* than the
    Lindelöf hypothesis (Lindelöf is `|ζ(½+it)| ≪ t^ε`; here the bound is a
    fixed power of `log t`). It is **unproven**, and in fact **false**:
    classical Ω-results (Titchmarsh §8; Montgomery) show `|ζ(½+it)|` exceeds any
    fixed power of `log t` for arbitrarily large `t`, so no such `C` exists.
    Moreover any *true* bound of comparable shape is itself a consequence of RH,
    so using it to prove RH is **circular**. The paper additionally cites a
    nonexistent "Lemma 5.1" at the contradiction step.

  * `ZeroRepulsion` — the paper's "standard zero-repulsion" step, here stated
    **conditionally**: *if* a nontrivial off-line zero exists, *then*
    `|ζ(½+it)|` is large infinitely often. It is asserted as "standard" in the
    fragment but is **not proved there** (and the precise lower bound is not
    available in mathlib v4.12.0).

  The combinator itself is a genuine Lean proof (classical-trio axioms, no
  `sorry`); the only substantive mathematics it performs is a pure-calculus
  comparison (`exp_loglog_dominates_sq`): for fixed `C, c₁ > 0`,
  `exp(c₁ log t / log log t)` eventually exceeds `C (log t)²`. That lemma carries
  no RH content — it merely powers the contradiction.

  **Non-vacuity.** `ZeroRepulsion` is deliberately *conditional* on an off-line
  zero existing. Were it stated unconditionally ("large values exist"), it would
  contradict `GrowthBound` outright and the combinator would collapse to
  ex-falso without using the calculus lemma. As stated, the two hypotheses are
  jointly satisfiable — e.g. in a world with no nontrivial off-line zeros,
  `ZeroRepulsion` holds vacuously and `GrowthBound` is unconstrained by it — so
  the combinator's proof genuinely exercises the comparison lemma.

  The target is the **real** Riemann Hypothesis as defined in mathlib
  (`_root_.RiemannHypothesis`, "constructing a term of this type is worth a
  million dollars"), aliased here as `RiemannHypothesisStmt`. The legacy
  `TheoremaAureum.RiemannHypothesis : Prop := True` stub in
  `lean-proof/TheoremaAureum/Certificates.lean` is deliberately untouched and is
  not imported; this file lives in the fresh `TheoremaAureum.Towers.RH`
  namespace (cf. `Towers/RH/ZeroDensity.lean`), so there is no name collision
  and no relabelling of a tautology as a theorem.

  Status: both hypotheses OPEN, undischarged. Proves NOTHING new about RH; makes
  NO "RH proved / Lindelöf proved" claim. SORRY: 0. NOT a brick.
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace TheoremaAureum
namespace Towers
namespace RH

open Filter

/-- The genuine Riemann Hypothesis, as defined in mathlib
    (`_root_.RiemannHypothesis`): every zero `s` of `riemannZeta` that is not a
    trivial zero and not the pole `s = 1` satisfies `s.re = 1/2`. We target this
    real statement rather than a weaker hand-rolled variant. -/
abbrev RiemannHypothesisStmt : Prop := _root_.RiemannHypothesis

/-- **The paper's growth Lemma (OPEN, and in fact false).**

    `∃ C > 0, ∀ t ≥ 2, |ζ(½+it)| ≤ C (log t)²`.

    Stronger than the Lindelöf hypothesis, unproven, false by classical
    Ω-results, and circular (any true comparable bound follows from RH). Carried
    as a named hypothesis; never discharged. -/
def GrowthBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t →
    Complex.abs (riemannZeta (1 / 2 + (t : ℂ) * Complex.I)) ≤ C * (Real.log t) ^ 2

/-- **The paper's zero-repulsion step (OPEN), stated conditionally.**

    *If* there is a nontrivial off-line zero `ρ` (i.e. `riemannZeta ρ = 0`,
    `ρ ≠ 1`, `ρ` not a trivial zero, `ρ.re ≠ 1/2`), *then* there is `c₁ > 0` such
    that `|ζ(½+it)| ≥ exp(c₁ log t / log log t)` for arbitrarily large `t`.

    Asserted as "standard" in the fragment but not proved there; the precise
    lower bound is unavailable in mathlib v4.12.0. Carried as a named
    hypothesis; never discharged. The conditional form keeps the combinator
    non-vacuous (see the file banner). -/
def ZeroRepulsion : Prop :=
  (∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ ≠ 1 ∧ (¬ ∃ n : ℕ, ρ = -2 * (n + 1)) ∧ ρ.re ≠ 1 / 2) →
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ B : ℝ, ∃ t : ℝ, B ≤ t ∧
      Real.exp (c₁ * Real.log t / Real.log (Real.log t))
        ≤ Complex.abs (riemannZeta (1 / 2 + (t : ℂ) * Complex.I))

/-- **Pure-calculus comparison (no RH content).**

    For fixed `C, c₁ > 0`, the zero-repulsion lower bound eventually dominates
    the growth upper bound:
    `C (log t)² < exp(c₁ log t / log log t)` for all sufficiently large `t`.

    Proof idea: substitute `v = log log t` (so `log t = exp v`); the claim
    becomes `log C + 2 v < c₁ exp v / v`, which holds for large `v` because
    `exp v / v²  → ∞`. -/
theorem exp_loglog_dominates_sq (C c₁ : ℝ) (hC : 0 < C) (hc₁ : 0 < c₁) :
    ∀ᶠ t in atTop,
      C * (Real.log t) ^ 2 < Real.exp (c₁ * Real.log t / Real.log (Real.log t)) := by
  have hexp2 : Tendsto (fun v : ℝ => Real.exp v / v ^ 2) atTop atTop :=
    Real.tendsto_exp_div_pow_atTop 2
  have hsub : Tendsto (fun v : ℝ => c₁ * (Real.exp v / v ^ 2) + (-2)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-2 : ℝ) (hexp2.const_mul_atTop hc₁)
  have hmul : Tendsto (fun v : ℝ => v * (c₁ * (Real.exp v / v ^ 2) + (-2))) atTop atTop :=
    tendsto_id.atTop_mul_atTop hsub
  have hcore : Tendsto (fun v : ℝ => c₁ * Real.exp v / v - 2 * v) atTop atTop := by
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with v hv
    have hv' : v ≠ 0 := ne_of_gt hv
    field_simp
    ring
  have hv_ineq : ∀ᶠ v in atTop, Real.log C + 2 * v < c₁ * Real.exp v / v := by
    filter_upwards [hcore.eventually_gt_atTop (Real.log C)] with v hv
    linarith
  have hloglog : Tendsto (fun t : ℝ => Real.log (Real.log t)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have ht_ineq := hloglog.eventually hv_ineq
  filter_upwards [ht_ineq, Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ)]
    with t htin htpos
  rw [Real.exp_log htpos] at htin
  have hCsq : C * (Real.log t) ^ 2
      = Real.exp (Real.log C + 2 * Real.log (Real.log t)) := by
    rw [Real.exp_add, Real.exp_log hC, two_mul, Real.exp_add, Real.exp_log htpos, ← pow_two]
  rw [hCsq, Real.exp_lt_exp]
  exact htin

/-- **Combinator (honest conditional reduction).**

    `GrowthBound → ZeroRepulsion → RiemannHypothesis`.

    A genuine Lean proof (classical-trio axioms, no `sorry`) — but it proves
    NOTHING new: both inputs are OPEN and undischarged, and `GrowthBound` is in
    fact false and circular (see the file banner). The proof: assume a
    nontrivial zero `s` with `s.re ≠ 1/2`; feed it to `ZeroRepulsion` to get
    arbitrarily large `|ζ(½+it)|`; bound those by `GrowthBound`; and contradict
    them via `exp_loglog_dominates_sq`. -/
theorem riemannHypothesis_of_growth_and_repulsion
    (hG : GrowthBound) (hR : ZeroRepulsion) : RiemannHypothesisStmt := by
  intro s hs htriv hs1
  by_contra hre
  obtain ⟨c₁, hc₁, hbig⟩ := hR ⟨s, hs, hs1, htriv, hre⟩
  obtain ⟨C, hC, hub⟩ := hG
  obtain ⟨Ta, hTa⟩ := eventually_atTop.mp (exp_loglog_dominates_sq C c₁ hC hc₁)
  obtain ⟨t, hBt, hge⟩ := hbig (max 2 Ta)
  have h2 : (2 : ℝ) ≤ t := le_trans (le_max_left _ _) hBt
  have hTat : Ta ≤ t := le_trans (le_max_right _ _) hBt
  have hub' := hub t h2
  have hcmp := hTa t hTat
  exact absurd (lt_of_le_of_lt (le_trans hge hub') hcmp) (lt_irrefl _)

end RH
end Towers
end TheoremaAureum
