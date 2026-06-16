#!/usr/bin/env bash
# Verify: no sorry/admit in Src/
set -e
if grep -rn 'sorry\|admit' Src/ 2>/dev/null | grep -v '^Binary'; then
  echo 'FAIL: sorry/admit found'
  exit 1
fi
echo 'PASS: 0 sorry/admit in Src/'
