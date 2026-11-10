#!/bin/bash
# usage: bash PCQK_summ.sh L003 ... : per scope, count of theorems with axioms lines and first errors
cd "$(dirname "$0")"
for a in "$@"; do f=PCQK_$a; echo "== $a $(python3 -I -c "import json;r=json.load(open('$f/receipt.json'));print(r['module'],r['exit_status'],len(r['print_axioms']))")"; xz -dc $f/stdout.log.xz | grep -E "error" | sed 's/.*PRVEq_//' | cut -c1-210 | head -${N:-4}; done
