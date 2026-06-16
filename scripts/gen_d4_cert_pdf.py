#!/usr/bin/env python3
"""Generate D4_w1_NEGATIVE_Certificate_2026-06-01.pdf (ASCII-only, fpdf2 core font)."""
from fpdf import FPDF

OUT = "lean-proof-towers/exports/D4_w1_NEGATIVE_Certificate_2026-06-01.pdf"

pdf = FPDF(format="A4")
pdf.set_auto_page_break(True, margin=15)
pdf.set_margins(18, 16, 18)
pdf.add_page()


def H(txt, size=12, gap=1.5):
    pdf.set_font("Helvetica", "B", size)
    pdf.multi_cell(0, 6, txt)
    pdf.ln(gap)


def P(txt, size=10, gap=1.0):
    pdf.set_font("Helvetica", "", size)
    pdf.multi_cell(0, 5, txt)
    pdf.ln(gap)


def BOX(txt, size=10):
    pdf.set_fill_color(245, 230, 230)
    pdf.set_font("Helvetica", "B", size)
    pdf.multi_cell(0, 5.5, txt, border=1, fill=True)
    pdf.ln(1.5)


H("D4 w1 Strict Bound -- NEGATIVE Certificate (2026-06-01)", 15, 2)
BOX("STATUS: VERIFIED_OUT_OF_TOWER_NEGATIVE\n"
    "D4 FAILS for beta = 0.86. Requires beta > 2.07942.")
BOX("DISCLAIMER: Numerical only. NOT Arb/MPFI. NOT Lean. NOT trio-clean. NOT mass gap.")

H("1. Statement under test", 12)
P("w1(beta) = integral_{SU(3)} exp(-beta * S(U)) d haar(U) < 1/7, at submitted beta = 0.86.\n"
  "Repo action: S(U) = plaquetteEnergy = (3 - Re tr U)/3   (WilsonPositivity.lean:27).")

H("2. Method", 12)
P("Deterministic Weyl integration over the SU(3) maximal torus\n"
  "  |Delta|^2 = prod_{j<k} (2 - 2 cos(t_j - t_k)),  t1,t2,t3 = -t1-t2,  self-normalized.\n"
  "Grid n = 2400. Cross-checked vs 2e6-draw Haar-SU(3) Monte Carlo.\n"
  "Validation: w1(0) = 1.000000 ; w1(0.86) = 0.432367 (quadrature) vs 0.4324 (MC) -- agree.")

H("3. Result", 12)
rows = [
    ("beta", "w1(beta)", "< 1/7 ?"),
    ("0.86", "0.432367", "NO"),
    ("1.00", "0.378821", "NO"),
    ("1.50", "0.238739", "NO"),
    ("2.00", "0.153058", "NO"),
    ("2.07942", "0.142857 (=1/7)", "boundary"),
    ("2.50", "0.099908", "YES"),
    ("3.00", "0.066441", "YES"),
]
w = [40, 60, 40]
pdf.set_font("Helvetica", "B", 10)
for i, c in enumerate(rows[0]):
    pdf.cell(w[i], 6, c, border=1, align="C")
pdf.ln()
pdf.set_font("Helvetica", "", 10)
for r in rows[1:]:
    for i, c in enumerate(r):
        pdf.cell(w[i], 6, c, border=1, align="C")
    pdf.ln()
pdf.ln(2)

H("4. Findings", 12)
P("1. D4 FAILS at beta = 0.86: w1(0.86) ~= 0.4324 ~= 3.0 x (1/7).\n"
  "2. Minimal threshold beta0 ~= 2.07942 -- bound holds only for beta > 2.07942.\n"
  "3. Submitted 0.85 was the un-normalized action (3 - Re tr = 3*S); the repo's\n"
  "   /3-normalization scales the threshold by ~3. Submitted value 0.0540459 is\n"
  "   reproduced by no tested normalization (withdrawn).")

H("5. Honesty locks / scope", 12)
P("- status_of_this_leaf: VERIFIED_OUT_OF_TOWER_NEGATIVE ; closes_D4: false ;\n"
  "  closes_mass_gap: false ; discharges_surface: false ; surface_1_status: OPEN ;\n"
  "  ym_tower_status: OPEN.\n"
  "- NEGATIVE verdict is numerically robust (0.4324 vs 0.1429). beta0 is a numerical\n"
  "  estimate, NOT a rigorous Arb/MPFI interval certificate.\n"
  "- OUT-OF-TOWER / Not Lean / Not trio-clean.\n"
  "- Even if re-established for beta > beta0: supplies only Wall256 hw1; nothing else.\n"
  "- Does NOT impact MassGap574.lean, Clay YM, or Surface #1 -- no mass-gap / mu>0 / m>0.\n"
  "- Does NOT close the Wall256 conditional (hOS, h_bridge OPEN) or KP.")

H("6. Termination", 12)
P("closes_leaf_D4: false. d4_verdict: TESTED NEGATIVE -- submitted bound false at\n"
  "beta=0.86 under repo action. minimal_beta0_repo_action: 2.07942.\n"
  "Parent KP surface, Surface #1, and the YM tower stay OPEN; no mass-gap / m>0 / Clay claim.")

pdf.output(OUT)
print("WROTE", OUT)
