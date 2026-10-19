#!/bin/bash
# Local focused compile of one NEW module (local-lean rules): flock, memory gate,
# -j1 -M4400 -DElab.async=false, /usr/bin/time -l receipt. Usage: compile.sh <Module>
set -u
M="$1"
HERE="$(cd "$(dirname "$0")" && pwd)"
SRC="$HERE/../../lean/$M.lean"
OBJ=/tmp/r1-overflow-free-20261019-objects
LP_BASE="$(cat "$HERE/lean_path.txt")"
export LEAN_PATH="$OBJ:$LP_BASE"
LEAN=/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
mkdir -p "$HERE/receipts"
while true; do
  free=$(vm_stat | awk '/Pages free/{f=$3} /Pages inactive/{i=$3} END{gsub("\\.","",f);gsub("\\.","",i);print (f+i)*16384}')
  [ "$free" -ge $((10*1024*1024*1024)) ] && break
  echo "waiting for memory: $free" >&2; sleep 60
done
SHA=$(shasum -a 256 "$SRC" | cut -d' ' -f1)
START=$(date -u +%Y-%m-%dT%H:%M:%SZ)
SWAP_BEFORE=$(sysctl -n vm.swapusage)
cd /tmp
python3 "$HERE/flock.py" /tmp/aspis-local-lean.lock /usr/bin/time -l "$LEAN" -j1 -M4400 -DElab.async=false -o "$OBJ/$M.olean" "$SRC" > "$HERE/receipts/$M.out" 2> "$HERE/receipts/$M.time"
EXIT=$?
SWAP_AFTER=$(sysctl -n vm.swapusage)
python3 - "$HERE" "$M" "$SHA" "$EXIT" "$START" "$SWAP_BEFORE" "$SWAP_AFTER" <<'PY'
import json,sys,re,os
here,m,sha,ex,start,sb,sa=sys.argv[1:]
t=open(f"{here}/receipts/{m}.time").read()
wall=re.search(r"([\d.]+) real",t); rss=re.search(r"(\d+)\s+maximum resident set size",t)
out=open(f"{here}/receipts/{m}.out").read()
ax=[l for l in out.splitlines() if "depends on axioms" in l or "does not depend on any axioms" in l]
rec={"module":m,"source":f"docs/research/100bit-spend-path-20261013/lean/{m}.lean","source_sha256":sha,
"exit":int(ex),"wall_s":float(wall.group(1)) if wall else None,"peak_rss_bytes":int(rss.group(1)) if rss else None,
"swap_before":sb,"swap_after":sa,"started_utc":start,"axioms":ax,
"errors":[l for l in out.splitlines() if ": error" in l][:40]}
open(f"{here}/receipts/{m}.json","w").write(json.dumps(rec,indent=1))
print(json.dumps({k:rec[k] for k in ("module","exit","wall_s","peak_rss_bytes")}))
PY
