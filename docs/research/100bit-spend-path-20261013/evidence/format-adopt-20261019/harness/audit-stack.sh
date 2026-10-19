#!/bin/sh
set -eu
H=/home/dombarker/project-offloads/codex-r1-format-adopt-20261019
for kind in verifier pool; do
    D=$H/stack/$kind
    mkdir -p "$D"
    cp "$H/artifacts/$kind/linked.elf" "$D/linked.elf"
    case "$kind" in
      verifier)
        cp "$H/artifacts/verifier/aspis_r1_cost_probe_program.so" "$D/stripped.so"
        cat "$H/receipts/sbf-verifier-1/stderr.log" "$H/receipts/sbf-verifier-program-guard/stderr.log" > "$D/build.log";;
      pool)
        cp "$H/artifacts/pool/aspis_pool.so" "$D/stripped.so"
        cp "$H/receipts/sbf-pool-adopt/stderr.log" "$D/build.log";;
    esac
    "$H/harness/capped-run.sh" "stack-$kind" "strict stack diagnostic inventory against complete linked ELF" "$H" -- python3 "$H/harness/strict-stack.py" "$D"
done
