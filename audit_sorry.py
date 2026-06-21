#!/usr/bin/env python3
"""
audit_sorry.py — Clay rules checker for yang-mills-gap
Strips comments and strings then searches for real `sorry` in proof terms.
Exit 0: clean. Exit 1: violations found.
"""
import re, sys
from pathlib import Path

pat_comment_block = re.compile(r'/-.*?-/', re.DOTALL)
pat_line_comment  = re.compile(r'--.*')
pat_string        = re.compile(r'"(?:\\.|[^"\\])*"', re.DOTALL)
pat_sorry         = re.compile(r'\bsorry\b')
pat_axiom         = re.compile(r'^\s*(?:@\[.*?\]\s*)?axiom\s+\w', re.MULTILINE)

hits = []
for f in sorted(Path('.').rglob('*.lean')):
    try:
        s = f.read_text(encoding='utf-8', errors='ignore')
    except Exception:
        continue
    t = pat_comment_block.sub('', s)
    t = pat_line_comment.sub('', t)
    t = pat_string.sub('', t)
    if pat_sorry.search(t) or pat_axiom.search(t):
        hits.append(str(f))

if hits:
    print("FAIL — real sorry/axiom hits in:")
    for h in hits:
        print(f"  {h}")
    sys.exit(1)
else:
    print("PASS — no real sorrys or non-trio axioms found (comment/docstring hits ignored)")
    sys.exit(0)
