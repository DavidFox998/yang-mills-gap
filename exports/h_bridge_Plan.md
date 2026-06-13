# h_bridge Dependency Map — Brydges-Federbush KP=>clustering bridge (Wall256 leaf D6)

plan_id: h_bridge_dependency_map
export_date: "2026-06-01"
scope: IN_TOWER_PLANNING_DOCS_ONLY — no .lean written, no proof, no numerics.

## What h_bridge is

Lean signature (Wall256_Scaffold.lean:85-86, hypothesis of strong_coupling_decay_of_open_inputs):
  (h_bridge : Summable (fun n : N => N n * a n) ->
      0 < rho ∧ rho < 1 ∧ forall x y, |corr x y| <= C * rho ^ (sep x y))

corr sep : E -> E -> R, C rho : R, N a : N -> R all ABSTRACT.
KP taxonomy: h_bridge = leaf D6, the Brydges-Federbush step.
Status: OPEN · OUT_OF_TOWER · in_mathlib_v4_12_0=false · stub_only.

## Open obligations

| # | obligation | status | tag |
|---|---|---|---|
| B0 | h_bridge itself | OPEN · OUT_OF_TOWER | NEEDS_LEMMA E3 (Brydges-Federbush) |
| B1 | Summable(N*a) premise (D3) | OPEN, blocked | BLOCKED_BY hOS + NEEDS_LEMMA D1 count |
| B2 | strict rho < 1 | OPEN | NEEDS_LEMMA (part of E3) |
| B3 | rho^d = exp(-Delta*d) algebra | PROVED (not an obligation) | Wall256_MassGapConditional.lean:88 |

Does certified beta0 discharge any? NO.
CERT_Arb has no direct numeric dependency in h_bridge; its beta-coupling is
indirect through hOS -> hw1 -> E1. B0/B2 are pure cluster-expansion analysis.

## Already proved (machine-checked, conditional — context only)

- kp_summable_of_truncatedActivity (Wall256_Note.lean:82, genuine comparison test, proved)
  Produces the Summable premise from TruncatedActivityBound + N n <= 7^n.
- su2_gap_of_truncatedActivity (Wall256_Note.lean:106, proved)
- mass_gap_pos_of_spectral_gap (Wall256_MassGapConditional.lean:88, proved)
  rho^d = exp(-Delta*d) algebra; conditional/abstract only.

These are proved but parametrized over open hypotheses — no unconditional mass-gap content.

## Minimal path (NOT scheduled)

1. hOS [BLOCKED_BY_Wall256, NEEDS_LEMMA] — TruncatedActivityBound(a) from OS Thm 2.1.
2. D1 entropy count [NEEDS_LEMMA] — instantiate N n <= 7^n for real polymer count (E2).
3. D3 summability — kp_summable_of_truncatedActivity (PROVED) yields Summable; no new work.
4. h_bridge [NEEDS_LEMMA] — formalize Brydges-Federbush with strict rho < 1 (E3).

Result: abstract LATTICE two-point decay shape ONLY — NOT Surface #1, NOT YM mass gap.

## When promoted to BUILD — STUBS ONLY

OK: def hBridge_Surface (...) : Prop := Summable (...) -> 0 < rho ∧ rho < 1 ∧ ...
OK: theorem h_bridge_of_surface (h : hBridge_Surface ...) : ... := h
NEVER: theorem h_bridge := by sorry
NEVER: axiom for Brydges-Federbush lemma

## Honesty locks

status: OPEN · OUT_OF_TOWER · in_mathlib:false
discharges_surface: false
closes_surface_1: false
result_if_all_inputs_close: "abstract LATTICE two-point decay shape ONLY — NOT Surface #1"
mass_gap_proven: false
surface_1_status: OPEN
ym_tower_status: OPEN
