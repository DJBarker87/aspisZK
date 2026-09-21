#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
${CXX:-g++} -std=c++17 -O2 -Wall -Wextra -Werror check_optimizations.cpp -o "$work/check"
"$work/check" | tee "$work/result.json"
python3 - "$work/result.json" <<'PY'
import json, sys
actual = json.load(open(sys.argv[1]))
expected = json.load(open('verification.json'))
assert actual == expected
PY
python3 generate_cyclic_tables.py --check
