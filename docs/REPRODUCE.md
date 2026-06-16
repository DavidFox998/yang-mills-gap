# Reproduce the KP Certificate

Prerequisites: leanprover/lean4:v4.12.0, Mathlib 809c3fb, Python 3.10+

Step 1 -- numerical enclosure:
    python3 scripts/arb_w1_enclosure.py
    # w1(beta_0) in (a,b) with b < 1/7 = 0.142857...

Step 2 -- Lean proof chain:
    cd lean-proof-towers && lake build KP
    lake env lean --run ../TheoremaAureum/YangMills/VerifyGap.lean
    # PASS: w1(beta_0) < 1/7  [107*7=749 < 756]

Step 3 -- axiom footprint:
    lake env lean ../TheoremaAureum/Clay.lean
    # output: propext, Classical.choice, Quot.sound
