#!/bin/bash
# usage: run_audit.sh <out-dir> <trace-run-dir>...   (each trace-run-dir = traces/<plan>/<label>)
# Splits every traced run into its three roles (stage-1 verifier = larger verifier
# invocation, nested stage-2 verifier = smaller one, Pool) and runs sbf_slack2.py
# once per role over all given runs.
H=/home/dombarker/project-offloads/codex-cx-cu-bound5-20261020
OUT=$1; shift; mkdir -p $OUT
VER=7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue; POOL=5PjDJaGfSPJj4tFzMRCiuuAasKg5n8dJKXKenhuwZexx
S1=(); S2=(); PO=()
for d in "$@"; do
  l=$(basename $d)
  v=$(for f in $d/*.regs; do b=${f%.regs}; [ "$(cat $b.program_id)" = $VER ] && echo "$(stat -c %s $f) $f"; done | sort -n)
  [ $(echo "$v" | wc -l) = 2 ] || { echo "expected 2 verifier invocations in $d"; exit 1; }
  s2=$(echo "$v" | head -1 | cut -d" " -f2); s1=$(echo "$v" | tail -1 | cut -d" " -f2)
  p=$(for f in $d/*.regs; do b=${f%.regs}; [ "$(cat $b.program_id)" = $POOL ] && echo $f; done)
  [ $(echo "$p" | wc -l) = 1 ] || { echo "expected 1 Pool invocation in $d"; exit 1; }
  S1+=(--trace $l=$s1); S2+=(--trace $l=$s2); PO+=(--trace $l=$p)
done
python3 $H/harness/sbf_slack2.py --linked $H/artifacts/verifier/linked.elf --deployed $H/artifacts/verifier/aspis_r1_cost_probe_program.so "${S1[@]}" --out $OUT/stage1.json || exit 1
python3 $H/harness/sbf_slack2.py --linked $H/artifacts/verifier/linked.elf --deployed $H/artifacts/verifier/aspis_r1_cost_probe_program.so "${S2[@]}" --out $OUT/stage2.json || exit 1
python3 $H/harness/sbf_slack2.py --linked $H/artifacts/pool/linked.elf --deployed $H/artifacts/pool/aspis_pool.so "${PO[@]}" --out $OUT/pool.json
