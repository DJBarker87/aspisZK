#!/bin/bash
# usage: bash PCVP_next.sh Module [maxerr]; runs the next free PCVP_Lnnn scope, prints id, exit status, errors
cd "$(dirname "$0")"
export PCVP_HOST_BASE=/home/dombarker/project-offloads/codex-pc-prov-p3p-20261110
m=$(ls -d PCVP_L[0-9][0-9][0-9] 2>/dev/null | sed 's/PCVP_L//' | sort -n | tail -1); m=$(grep -ho 'PCVP_L[0-9]\{3\}' PCVP_ATTEMPTS.jsonl | sed 's/PCVP_L//' | sort -n | tail -1)
id=$(printf PCVP_L%03d $((10#$m+1)))
echo "== $id $1"
bash PCVP_go.sh $id $1 ${2:-12} 2>&1 | python3 -c "
import sys,re
t=sys.stdin.read()
m=re.search(r'\"exit_status\": (\d+), \"wall_seconds\": ([\d.]+), \"peak_rss_kib\": \"(\d+)\"',t)
print('exit',m.groups() if m else t[-400:])
print('\n'.join(l[:300] for l in t.splitlines() if 'error' in l))
"
