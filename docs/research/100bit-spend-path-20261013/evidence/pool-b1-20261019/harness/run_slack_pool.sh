#!/bin/bash
# Pool-only syscall/branch audit of the traced settlements (one output per kind).
# no set -e: the program-id filter loop returns 1 on its last non-matching file
cd /home/dombarker/project-offloads/codex-r1-pool-b1-20261019/traces
for KIND in transfer withdrawal; do
  PO=()
  for d in trace-*-$KIND-*; do
    p=$(for f in $d/*.regs; do b=${f%.regs}; [ "$(cat $b.program_id)" = 5PjDJaGfSPJj4tFzMRCiuuAasKg5n8dJKXKenhuwZexx ] && echo $f; done)
    PO+=(--trace $d=$p)
  done
  mkdir -p /home/dombarker/project-offloads/codex-r1-pool-b1-20261019/analysis
  python3 /home/dombarker/project-offloads/codex-r1-pool-b1-20261019/harness/sbf_slack.py --linked /home/dombarker/project-offloads/codex-r1-pool-b1-20261019/artifacts/pool/linked.elf --deployed /home/dombarker/project-offloads/codex-r1-pool-b1-20261019/artifacts/pool/aspis_pool.so "${PO[@]}" --out /home/dombarker/project-offloads/codex-r1-pool-b1-20261019/analysis/pool-$KIND.json
done
