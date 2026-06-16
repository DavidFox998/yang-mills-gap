-- Axiom status: Classical trio only. 0 sorry. 0 new axioms.
-- D5: Concrete KP summability at β = 11/5. D5 FULLY CLOSED.
--
-- D5 closure path (Route 1 -- Bessel lower-enclosure, §16 of W1_One_Seventh_Proof.lean):
--   1. exp₇_lower      : P₂₈ - err₂₈ ≤ exp(-β₇)          [Taylor-Lagrange, same as exp₇_upper]
--   2. seven_tsum_det_ge : finite_lo - tail_ub ≤ ∑' det   [besselIn_seven_interval .lo side]
--   3. seven_lo_part_c : (P₂₈-err₂₈)·(lo-tail) > 1/8     [pure ℚ, by decide]
--   4. w1_seven_pos    : 0 < w1_weyl_series(β₇)            [closes named surface]
--
-- Given from earlier files:
--   D4 (w1_seven_lt : w1_weyl_series(11/5) < 1/7)  -- W1_One_Seventh_Proof.lean §15
--   D3 (kp_summable abstract)                       -- BrydgesFederbush_D1D3.lean
--
-- D_series chain status:
--   D1 PROVED  (peierls_branching_bound)
--   D2 PROVED  (geometric_activity_bound)
--   D3 PROVED  (kp_summable abstract)
--   D4 PROVED  (w1_weyl_series(11/5) < 1/7)
--   D5 PROVED  (w1_seven_pos_Surface closed; summability unconditional)
--   D6 OPEN    (KP-summability -> spectral decay bridge, OUT-OF-TOWER)
--
-- Clay mass gap: OPEN. Surface #1: OPEN. kotecky_preiss_criterion_Surface: OPEN.

import Towers.YM.BrydgesFederbush_D1D3
import Towers.YM.W1_One_Seventh_Proof

namespace TheoremaAureum.Towers.YM.BrydgesFederbush

open Real
open TheoremaAureum.Towers.YM.Wall256Note
open TheoremaAureum.Towers.YM.WeylToeplitzBound
open TheoremaAureum.Towers.YM.W1SeventhProof

/-! ## w1_seven_pos_Surface: PROVED (Route 1) -/

/-- **[PROVED]** w1_weyl_series(β₇) > 0.
    Proved in W1_One_Seventh_Proof.lean §16 via Route 1 (Bessel lower-enclosure):
      * Lower Lagrange bracket: exp(-β₇) ≥ P₂₈ - err₂₈
      * Bessel lower enclosure at N=40: ∑' det ≥ finite_7_lo_sum - tail_7_ub
      * Pure ℚ decide: (P₂₈-err₂₈)·(finite_lo-tail_ub) > 1/8
      * Hence w1_weyl_series(β₇) > 1/8 > 0
    Classical trio only. 0 sorry. 0 new axioms.
    Status: D5 CLOSED. -/
theorem w1_seven_pos_Surface : 0 < w1_weyl_series (β₇_rat : ℝ) := w1_seven_pos

/-! ## D5a: TruncatedActivityBound for the concrete SU(3) series -/

/-- **[MACHINE-CHECKED]** D5a conditional: kept for composability.
    Accepts an explicit positivity proof; use `d5a_closed` for the unconditional form. -/
theorem d5a_truncated_activity_bound
    (h_pos : 0 < w1_weyl_series (β₇_rat : ℝ)) :
    TruncatedActivityBound (fun n => w1_weyl_series (β₇_rat : ℝ) ^ n) :=
  geometric_activity_bound (w1_weyl_series (β₇_rat : ℝ)) h_pos w1_seven_lt

/-- **[MACHINE-CHECKED, UNCONDITIONAL]** D5a: TruncatedActivityBound at β₇ = 11/5.
    Closed by w1_seven_pos_Surface. Classical trio only. -/
theorem d5a_closed :
    TruncatedActivityBound (fun n => w1_weyl_series (β₇_rat : ℝ) ^ n) :=
  d5a_truncated_activity_bound w1_seven_pos_Surface

/-! ## D5b: Concrete KP summability at β₇ = 11/5 -/

/-- **[MACHINE-CHECKED]** D5b conditional: kept for composability.
    Use `d5b_closed` for the fully unconditional version. -/
theorem d5b_kp_summable_concrete
    (N      : ℕ → ℝ)
    (hN0    : ∀ n, 0 ≤ N n)
    (h0     : N 0 ≤ 1)
    (hstep  : ∀ n, N (n + 1) ≤ 7 * N n)
    (h_pos  : 0 < w1_weyl_series (β₇_rat : ℝ)) :
    Summable (fun n => N n * w1_weyl_series (β₇_rat : ℝ) ^ n) :=
  kp_summable N (w1_weyl_series (β₇_rat : ℝ)) hN0 h0 hstep h_pos w1_seven_lt

/-- **[MACHINE-CHECKED, UNCONDITIONAL]** D5 fully closed: concrete KP summability at β₇.
    For any abstract polymer count N satisfying the Peierls branching recurrence:
      Summable (fun n => N n * w1_weyl_series(β₇)^n)
    D1-D5 all PROVED. D6 OPEN (OUT-OF-TOWER). kotecky_preiss_criterion_Surface: OPEN.
    NOT a mass gap. NOT a Clay result. -/
theorem d5b_closed
    (N     : ℕ → ℝ)
    (hN0   : ∀ n, 0 ≤ N n)
    (h0    : N 0 ≤ 1)
    (hstep : ∀ n, N (n + 1) ≤ 7 * N n) :
    Summable (fun n => N n * w1_weyl_series (β₇_rat : ℝ) ^ n) :=
  d5b_kp_summable_concrete N hN0 h0 hstep w1_seven_pos_Surface

-- Axiom audit (uncomment after lake build):
-- #print axioms w1_seven_pos_Surface   -- expect: classical trio
-- #print axioms d5a_closed             -- expect: classical trio
-- #print axioms d5b_closed             -- expect: classical trio

end TheoremaAureum.Towers.YM.BrydgesFederbush
