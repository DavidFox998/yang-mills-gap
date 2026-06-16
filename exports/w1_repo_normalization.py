#!/usr/bin/env python3
"""
w1_repo_normalization.py
Single-plaquette SU(3) Haar weight under the REPO action normalization:
    w1(beta) = integral_{SU(3)} exp(-beta * S(U)) d haar(U)
    S(U) = plaquetteEnergy(U) = (3 - Re tr U)/3 = 1 - (Re tr U)/3
(Towers/YM/WilsonPositivity.lean:27 ; Towers/YM/WilsonAction.lean:134).

Method: deterministic Weyl integration over the SU(3) maximal torus.
  eigenangles t1,t2,t3 = -t1-t2 ; Re tr U = cos t1 + cos t2 + cos t3 ;
  Weyl density |Delta|^2 = prod_{j<k} (2 - 2 cos(tj - tk)) ;
  w1(beta) = (integral exp(-beta S) |Delta|^2) / (integral |Delta|^2)  [self-normalized].

VALIDATION (n=2400): w1(0)=1.000000 ; w1(0.86)=0.432367
  (Monte Carlo, 2e6 Haar-SU(3) draws, gives 0.4324 -> agree).
RESULT: minimal beta0 with w1(beta0)=1/7 is beta0 ~= 2.07942.
  => w1(0.86)=0.4324 > 1/7 : D4 FAILS at beta=0.86 under repo action.

CLOSED FORM (2026-06-01): w1 has an EXACT Bessel-determinant closed form -- a
WINDING SUM of shifted 3x3 Toeplitz determinants over the SU(3) U(1) det-charge:
    w1(beta) = e^{-beta} * sum_{k in Z} det[ I_{(i-j)+k}(beta/3) ]_{i,j=0,1,2}.
Derivation: w1 = E[exp(-(beta/3)(3 - Re tr U))] = e^{-beta} * E[exp((beta/3) Re tr U)];
the SU(3) Haar average of exp(g Re tr U) is the winding sum of the U(3)
Gross-Witten Toeplitz-Bessel determinant  int_{U(3)} exp(g Re tr U) dU =
det[I_{i-j}(g)]  (I_{-n}=I_n), summed over the determinant charge k to project
U(3) -> SU(3). See w1_closed_form() below. Verified vs the grid quadrature AND the
rigorous CERT_Arb_beta0 interval certificate (converges by K=3):
    w1(0.86)    = 0.432367492091  (cert 0.4323674920909..)
    w1(2.07942) = 0.142856757048  (cert 0.1428567570476.. ; < 1/7).

WRONG closed forms (recorded so they do NOT resurface):
  * I_1(2b)*I_0(2b)/b^2                 -- off by ~9x; NOT the SU(3) integral.
  * exp(-3b)*det[I_{i-j}(2b)]/b^2       -- = 0.029 at beta0, NOT 1/7. Three errors:
      a SINGLE det is the U(3) (not SU(3)) integral, the 2b argument and the /b^2
      are spurious. (U(3) det[I(b)] at beta0 = 2.94 vs SU(3) avg 3.81.)
  * The 3x3 Toeplitz det expands to  I0^3 - 2 I0 I1^2 + 2 I1^2 I2 - I0 I2^2,
      NOT  I0^2 I2 + 2 I0 I1^2 - I1^2 I2 - 2 I0 I1^2  (whose middle terms cancel
      to I2(I0^2-I1^2); 310 vs the correct 64.15 at beta0).

OUT-OF-TOWER: numerical only; NOT a Lean object, NOT trio-clean, NOT a rigorous
(Arb/MPFI) interval certificate. Establishes only a numerical estimate. The
closed form AGREES with the existing grid + CERT_Arb values: it changes NO w1
value, NO beta0, and discharges NO surface. w1 stays opaque in Lean (Wall256
hw1); KP surface, Surface #1, and the YM tower stay OPEN.
"""
import numpy as np


def build_grid(n=2400):
    t = np.linspace(-np.pi, np.pi, n, endpoint=False)
    dt = 2 * np.pi / n
    T1, T2 = np.meshgrid(t, t, indexing="ij")
    T3 = -T1 - T2
    chord = lambda a: 2 - 2 * np.cos(a)
    D2 = chord(T1 - T2) * chord(T1 - T3) * chord(T2 - T3)   # |Delta|^2
    S = 1 - (np.cos(T1) + np.cos(T2) + np.cos(T3)) / 3.0    # repo plaquetteEnergy
    return S, D2, dt


S, D2, DT = build_grid()
Z = np.sum(D2) * DT * DT


def w1(beta):
    return float(np.sum(np.exp(-beta * S) * D2) * DT * DT / Z)


def w1_closed_form(beta, K=12):
    """Truncated evaluator of the EXACT infinite-series closed form of w1 (see
    module docstring). The exact identity is the infinite winding sum

        w1(beta) = e^{-beta} * sum_{k in Z} det[ I_{(i-j)+k}(beta/3) ]_{i,j=0,1,2};

    this function returns the symmetric partial sum over k = -K..K. The series
    converges geometrically (terms ~ I_{|k|}(beta/3) decay super-exponentially in
    |k|), so K=3 already saturates double precision for the beta of interest --
    the K=-K..K truncation is a numerically negligible approximation, not the
    exact value by itself. It agrees with the grid quadrature w1() and the
    rigorous CERT_Arb_beta0 interval certificate. Uses mpmath (already a repo
    dependency via arb_w1_enclosure.py) for I_n and the determinant.
    """
    import mpmath as mp

    g = mp.mpf(repr(beta)) / 3
    total = mp.mpf(0)
    for k in range(-K, K + 1):
        M = mp.matrix(3, 3)
        for i in range(3):
            for j in range(3):
                M[i, j] = mp.besseli((i - j) + k, g)
        total += mp.det(M)
    return float(mp.e ** (-mp.mpf(repr(beta))) * total)


def beta0(target=1.0 / 7.0, lo=0.5, hi=8.0, iters=80):
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        if w1(mid) < target:
            hi = mid
        else:
            lo = mid
    return 0.5 * (lo + hi)


def mc_check(n=2_000_000, beta=0.86, seed=0):
    """Optional independent Monte-Carlo validation over Haar SU(3)."""
    rng = np.random.default_rng(seed)
    Zc = (rng.standard_normal((n, 3, 3)) + 1j * rng.standard_normal((n, 3, 3))) / np.sqrt(2)
    Q, R = np.linalg.qr(Zc)
    d = np.einsum("...ii->...i", R)
    Q = Q * (d / np.abs(d))[:, None, :]
    U = Q / (np.linalg.det(Q) ** (1 / 3))[:, None, None]
    Re = np.einsum("...ii->...", U).real
    return float(np.mean(np.exp(-beta * (1 - Re / 3.0))))


if __name__ == "__main__":
    assert abs(w1(0.0) - 1.0) < 1e-6, "normalization check failed"
    print("w1(0)      =", round(w1(0.0), 6), "(must be 1.0)")
    print("w1(0.86)   =", round(w1(0.86), 6), " < 1/7 ?", w1(0.86) < 1 / 7)
    b0 = beta0()
    print("1/7        =", 1 / 7)
    print("minimal beta0 (repo action) =", round(b0, 5))
    print("w1(beta0)  =", round(w1(b0), 6), "; w1(beta0+0.01) =", round(w1(b0 + 0.01), 6))
    # Bessel-determinant closed form vs the grid quadrature (and CERT_Arb values).
    cf_086 = w1_closed_form(0.86)
    cf_b0 = w1_closed_form(2.07942)
    print("closed-form w1(0.86)    =", round(cf_086, 6), "(grid", round(w1(0.86), 6), ")")
    print("closed-form w1(2.07942) =", round(cf_b0, 6), "(grid", round(w1(2.07942), 6), ")")
    assert abs(cf_086 - w1(0.86)) < 1e-4 and abs(cf_b0 - w1(2.07942)) < 1e-4, "closed form mismatch"
    # print("MC w1(0.86) =", round(mc_check(), 6))  # uncomment for the 2e6-draw cross-check
