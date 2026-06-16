#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
echo "=== YM Tower SHA Manifest ==="
echo "Date: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
find "$ROOT/TheoremaAureum" -name '*.lean' | sort | while read f; do
  echo "$(sha256sum "$f" | cut -d' ' -f1)  ${f#$ROOT/}"
done
