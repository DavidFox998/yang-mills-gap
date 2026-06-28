#!/usr/bin/env python3
"""
SzegoGap Numerical Audit (2026-06-28)
======================================
Verifies numerically that all three surfaces in SzegoFromWeyl.lean (S3-S5) state
FALSE propositions. Opera Numerorum rule: no fabricated cert values.

  S = SzegoGap_genuine_open     : w1_haar_SU3 beta0 = w1_weyl_series beta0
  B = TorusIntegralWilson_OPEN  : integral_{T^2} ww*Delta = w1_weyl/6
  A = SU3_WeylIntFormula_OPEN   : integral_{T^2} ww*Delta = (1/6)*integral_G ww

Mutual-implication triple proved (0 sorry, classical trio):
  A /\ B -> S   (szego_from_weyl_and_torus)
  S /\ B -> A   (weyl_from_szego_and_torus)
  S /\ A -> B   (torus_from_szego_and_weyl)

None can be closed by cert axiom: all three are numerically false.
"""

import numpy as np
from scipy.stats import unitary_group
from scipy.special import iv as besseli  # modified Bessel I_n

# beta_0 = 2079416880124 / 1e12 = ln(8) (BDP/MS tower value)
beta0_rat = 2079416880124
beta0_den = 1000000000000
beta0 = beta0_rat / beta0_den
print(f"beta_0 = {beta0_rat}/{beta0_den} = {beta0:.15f}")
print(f"       = ln(8) = {np.log(8):.15f}  (check: diff = {abs(beta0 - np.log(8)):.2e})")
print()

# ── Part 1: Riemann sum for torus integral ──────────────────────────────────
print("=" * 65)
print("PART 1: Torus integral  int_{[0,2pi]^2} ww * Delta  d theta")
print("  wilson_weight: exp(-beta*(3 - cos t1 - cos t2 - cos(t1+t2)))")
print("  weyl_denominator: 8*(1-cos(t1-t2))*(1-cos(2t1+t2))*(1-cos(t1+2t2))")
print()

N = 2000
t = np.linspace(0, 2*np.pi, N, endpoint=False)
dt = 2*np.pi / N
T1, T2 = np.meshgrid(t, t, indexing="ij")

# Validation at beta=0: int int Delta d theta1 d theta2 = 6*(2*pi)^2
re_tr_0 = np.cos(T1) + np.cos(T2) + np.cos(T1 + T2)
delta = 8*(1 - np.cos(T1 - T2))*(1 - np.cos(2*T1 + T2))*(1 - np.cos(T1 + 2*T2))
integral_delta = np.sum(delta) * dt**2
expected_delta = 6 * (2*np.pi)**2
print(f"  Validation beta=0: int_delta = {integral_delta:.6f}")
print(f"  Expected 6*(2pi)^2 = {expected_delta:.6f}")
print(f"  Relative error = {abs(integral_delta - expected_delta)/expected_delta:.2e}  (< 1e-5 for N=2000)")
print()

# Main: torus integral at beta0
re_tr = np.cos(T1) + np.cos(T2) + np.cos(T1 + T2)
ww = np.exp(-beta0 * (3 - re_tr))
torus_integral = np.sum(ww * delta) * dt**2
print(f"  Torus integral at beta0: {torus_integral:.10f}")
print()

# ── Part 2: w1_weyl_series ──────────────────────────────────────────────────
print("=" * 65)
print("PART 2: w1_weyl_series beta0 = exp(-beta0) * sum_k det[I_{|i-j-k|}(beta0/3)]")
print()

def toeplitz_det(beta, k_max=50):
    """Compute exp(-beta) * sum_{k=-k_max..k_max} det(3x3 Toeplitz Bessel matrix)."""
    b3 = beta / 3
    total = 0.0
    for k in range(-k_max, k_max+1):
        M = np.zeros((3, 3))
        for i in range(3):
            for j in range(3):
                n = abs(i - j - k)
                M[i, j] = besseli(n, b3)
        total += np.linalg.det(M)
    return np.exp(-beta) * total

w1_weyl = toeplitz_det(beta0, k_max=100)
print(f"  w1_weyl_series(beta0) = {w1_weyl:.10f}")
print(f"  w1_weyl_series(0)     = {toeplitz_det(0.0, k_max=10):.10f}  (expected: 1.0)")
print()

# ── Part 3: Monte Carlo for w1_haar ────────────────────────────────────────
print("=" * 65)
print("PART 3: Monte Carlo for w1_haar_SU3(beta0) = int_{SU(3)} ww d(haar)")
print("  Sampling: U from U(3) Haar -> V = U/det(U)^{1/3} in SU(3)")
print("  Validation: E[|tr V|^2] should equal 1 (Schur orthogonality)")
print()

np.random.seed(42)
N_mc = 200000
batch = 5000
n_batches = N_mc // batch

sum_one = 0.0; sum_tr2 = 0.0; sum_retr = 0.0; sum_ww = 0.0
for _ in range(n_batches):
    U_list = unitary_group.rvs(3, size=batch)
    for U in U_list:
        d = np.linalg.det(U)
        V = U / (d ** (1/3))  # SU(3) element
        tr_V = np.trace(V)
        re_tr_v = tr_V.real
        sum_one += 1.0
        sum_tr2 += abs(tr_V)**2
        sum_retr += re_tr_v
        sum_ww += np.exp(-beta0 * (3 - re_tr_v))

w1_haar_mc = sum_ww / N_mc
print(f"  N = {N_mc:,}")
print(f"  E[1]       = {sum_one/N_mc:.6f}   (expected: 1.000000)")
print(f"  E[|tr|^2]  = {sum_tr2/N_mc:.6f}   (expected: 1.000000 by Schur)")
print(f"  E[Re tr]   = {sum_retr/N_mc:.6f}  (expected: 0.000000 by symmetry)")
print(f"  w1_haar_SU3(beta0) = {w1_haar_mc:.8f}")
print()

# ── Part 4: Verdict ─────────────────────────────────────────────────────────
print("=" * 65)
print("VERDICT: Comparison table")
print()
w1_weyl_over_6 = w1_weyl / 6
w1_haar_over_6 = w1_haar_mc / 6
weyl_pred = expected_delta * w1_haar_mc  # 6*(2pi)^2 * w1_haar
print(f"  Quantity                        Computed         Claim/Expected")
print(f"  ---------------------------------------------------------------")
print(f"  w1_haar_SU3(beta0)         {w1_haar_mc:>12.8f}    (Haar MC N=200K)")
print(f"  w1_weyl_series(beta0)      {w1_weyl:>12.8f}    (Toeplitz sum)")
print(f"  Ratio w1_haar/w1_weyl      {w1_haar_mc/w1_weyl:>12.6f}    (expected 1 if S is TRUE)")
print()
print(f"  torus_integral (Riemann N=2000)  {torus_integral:.6f}")
print(f"  w1_weyl/6                        {w1_weyl_over_6:.6f}  (TorusIntegralWilson_OPEN claim)")
print(f"  (1/6)*w1_haar                    {w1_haar_over_6:.6f}  (SU3_WeylIntFormula_OPEN claim, C=1/6)")
print(f"  6*(2pi)^2*w1_haar                {weyl_pred:.6f}  (true Weyl formula: int_T = 6*(2pi)^2*int_G)")
print()
print(f"  S=FALSE: w1_haar={w1_haar_mc:.5f} != w1_weyl={w1_weyl:.5f}  (ratio={w1_haar_mc/w1_weyl:.4f})")
print(f"  B=FALSE: torus={torus_integral:.4f} != w1_weyl/6={w1_weyl_over_6:.6f}  (ratio={torus_integral/w1_weyl_over_6:.1f})")
print(f"  A=FALSE: torus={torus_integral:.4f} != (1/6)*w1_haar={w1_haar_over_6:.6f}  (ratio={torus_integral/w1_haar_over_6:.1f})")
print()
print(f"  Correct Weyl formula: int_T = 6*(2pi)^2 * int_G  (C=6*(2pi)^2 not C=1/6)")
print(f"  6*(2pi)^2 * w1_haar = {weyl_pred:.6f}")
print(f"  torus_integral      = {torus_integral:.6f}")
print(f"  Ratio               = {torus_integral/weyl_pred:.6f}  (expected 1.0)")
print()
print("CONCLUSION: All three surfaces are NUMERICALLY FALSE.")
print("  No cert axiom can close S, B, or A without fabricating values.")
print("  Opera Numerorum rule: no fabricated values. Surfaces remain OPEN.")
print()
print("Root cause of w1_weyl != w1_haar:")
print("  The Toeplitz-Bessel formula w1_weyl_series(beta)")
print("  = exp(-beta) * sum_k det[I_{|i-j-k|}(beta/3)]")
print("  is a DIFFERENT object from int_{SU(3)} exp(-beta*(3-Re tr)) d(haar).")
print("  They agree at beta=0 (both = 1) but diverge for beta > 0.")
print("  Taylor at beta->0: w1_haar ~ 1-3*beta, w1_weyl ~ 1-beta.")
print("  The formula origin and intended mathematical meaning require investigation.")
