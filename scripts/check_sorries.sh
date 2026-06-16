#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
FOUND=$(grep -rn --include='*.lean' '\bsorry\b' "$ROOT/TheoremaAureum/" || true)
if [ -n "$FOUND" ]; then echo "FAIL: sorry found"; echo "$FOUND"; exit 1; fi
echo "PASS: no sorry in TheoremaAureum/"
