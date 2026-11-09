#!/bin/bash
# read-only recovery of a finished host attempt: bash recover.sh PCUD_L013
a=$1
B=/home/dombarker/project-offloads/codex-pc-prov-p2d-20261109
cd /Users/dominic/ZK/.worktrees/pc-prov-p2d/evidence/prov-p2d-20261109
mkdir -p $a
for f in receipt.json time.log stdout.log; do
  timeout 120 ssh -o ConnectTimeout=20 -o ServerAliveInterval=15 dombarker@100.108.41.90 "cat $B/$a/$f" > $a/$f || echo "fail $f"
done
timeout 60 ssh -o ConnectTimeout=20 dombarker@100.108.41.90 "cat $B/$a.json" > $a.json
for f in stdout.log time.log; do sha256sum $a/$f | cut -d' ' -f1 > $a/$f.sha256; xz -f -6 $a/$f; done
python3 -c "
import json;r=json.load(open('$a/receipt.json'));print({k:r[k] for k in ['exit_status','wall_seconds','peak_rss_kib','swaps']})"
