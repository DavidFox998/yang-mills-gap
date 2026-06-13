# hOS Dependency Map — Osterwalder-Seiler cluster step (Wall256 leaf D5)

plan_id: hOS_dependency_map
export_date: "2026-06-01"
scope: IN_TOWER_PLANNING_DOCS_ONLY — no .lean written, no proof, no numerics.

## What hOS is

Lean signature (Wall256_Scaffold.lean:84, hypothesis of strong_coupling_decay_of_open_inputs):
  (hOS : w1 < 1 / 7 → TruncatedActivityBound a)

where (Wall256_Note.lean:72):
  def TruncatedActivityBound (a : N → R) : Prop :=
    (forall n, 0 <= a n) ∧ exists I : R, Real.log 7 < I ∧ forall n, a n <= Real.exp (-I) ^ n

KP taxonomy: hOS = leaf D5, the Osterwalder-Seiler 1978 Thm 2.1 strong-coupling
Ursell/cluster step (single-site smallness => truncated connected-polymer activity
rate I > log 7). NOT OS reflection positivity.

Status: OPEN · OUT_OF_TOWER · in_mathlib_v4_12_0=false · stub_only.

## Open obligations

| # | obligation | status | tag |
|---|---|---|---|
| H0 | hOS : w1<1/7 -> TruncatedActivityBound a | OPEN · OUT_OF_TOWER | NEEDS_LEMMA E4 |
| H1 | antecedent w1 < 1/7 (scalar hw1) | OPEN | BLOCKED_BY_Wall256 + NEEDS_NUMERICS E1 |
| H2 | strict rate I with log 7 < I | OPEN | NEEDS_LEMMA (OS must deliver strict I>log7) |
| H3 | nonneg: forall n, 0 <= a n | OPEN | NEEDS_LEMMA (trivial once a=polymerActivity) |

Does the certified beta0 discharge any? NO.
CERT_Arb (beta0 in [2.079416880123, 2.079416880124]) is OUT-OF-TOWER interval
numerics, not a Lean term. H0/H2/H3 are pure cluster-expansion analysis (E4),
untouched by beta0. H1 gets a numeric shape but remains unformalized.

## Minimal path to realize hOS (NOT scheduled)

1. Bridge hw1 [BLOCKED_BY_Wall256] — thread Beta0Certified into the scalar w1<1/7 premise.
2. Port SU(3) single-site numeric [NEEDS_NUMERICS] — Lean proof of w1<1/7 for beta>2.079416880124.
   (CERT_Arb is out-of-tower; Lean needs SU(3) char theory or verified cubature — absent v4.12.0.)
3. Formalize Osterwalder-Seiler Thm 2.1 [NEEDS_LEMMA] — Ursell/cluster bound delivering I>log7.
4. Instantiate a := polymerActivity [NEEDS_LEMMA] — discharge H3/H2 against real activity.

None is scheduled. Steps 2-4 are open research or absent from mathlib v4.12.0.

## When promoted to BUILD — STUBS ONLY

OK: def hOS_Surface (w1 : R) (a : N -> R) : Prop := w1 < 1/7 -> TruncatedActivityBound a
OK: theorem hOS_of_surface (h : hOS_Surface w1 a) : ... := h
NEVER: theorem hOS := by sorry (emits sorryAx)
NEVER: axiom for OS lemma (off classical trio)

## Honesty locks

status: OPEN · OUT_OF_TOWER · in_mathlib:false
discharges_surface: false
closes_surface_1: false
mass_gap_proven: false
surface_1_status: OPEN
ym_tower_status: OPEN
