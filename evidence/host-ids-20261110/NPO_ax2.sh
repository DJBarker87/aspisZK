#!/bin/bash
# NPO_ raw ax2 walk with ledger30's pinned walker (sha256 46ee271b...), inside an 8G capped scope.
# Usage: NPO_ax2.sh <label> <Module> <comma roots>
set -u
[ "$(pgrep -c -x lean)" -lt 6 ] || { echo "HOST LEAN COUNT >= 6"; exit 4; }
W=/home/dombarker/project-offloads/codex-cx-hostids-20261110
R=/home/dombarker/project-offloads/codex-cx-replay-l187-20261109
T=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0
WALK=/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNM_20261111/NNM_native/NNM_ProofDriver
L=$1; M=$2; ROOTS=$3; D=$W/logs/$L; mkdir -p $D/audit
[ "$(sha256sum $WALK | cut -d' ' -f1)" = 46ee271b392729449147b978830b474e3fa4ecba2b45e03ad13c02490ba6ca3c ] || { echo WALKER PIN MISMATCH; exit 6; }
python3 - "$D" "$M" "$ROOTS" <<'PY'
import json,sys
d,m,roots=sys.argv[1],sys.argv[2],sys.argv[3].split(',')
open(d+'/audit/NLX_AUDIT_ROOTS.json','w').write(json.dumps(dict(roots=roots,groups=[roots])))
open(d+'/audit/NLX_AUDIT_MODULES.json','w').write(json.dumps([[m]]))
PY
cd $D/audit
systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  env -i PATH=/usr/bin:/bin LEAN_SYSROOT=$T LEAN_PATH=$W/out:$R/objs:$R/base_ref TMPDIR=$W/tmp \
  /usr/bin/time -v -o $D/time.log timeout 180 $WALK proof0 > $D/stdout.log 2>&1
ec=$?
rss=$(grep 'Maximum resident' $D/time.log | awk '{print $NF}'); wall=$(grep 'Elapsed (wall' $D/time.log | awk '{print $NF}'); swap=$(grep 'Swaps' $D/time.log | awk '{print $NF}')
printf '{"label":"%s","module":"%s","roots":"%s","walker_sha256":"46ee271b392729449147b978830b474e3fa4ecba2b45e03ad13c02490ba6ca3c","exit":%s,"wall":"%s","peak_rss_kib":"%s","swaps":"%s","caps":"MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64; timeout 180"}\n' "$L" "$M" "$ROOTS" "$ec" "$wall" "$rss" "$swap" > $D/receipt.json
cat $D/receipt.json; tail -8 $D/stdout.log
