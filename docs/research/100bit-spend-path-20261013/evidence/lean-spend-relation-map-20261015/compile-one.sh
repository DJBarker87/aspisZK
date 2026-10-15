#!/bin/bash
set -u
T=/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013
# The known external 24 GiB reservation covers the finite Docker scopes.
# Count active scopes recursively, reserving at least 24 GiB for that group.
reserved_gib=$(python3 - <<'RESERVATION'
from pathlib import Path
root=Path('/sys/fs/cgroup')
external=0
other=0
for f in root.rglob('memory.max'):
    if not f.parent.name.endswith('.scope'):
        continue
    v=f.read_text().strip()
    if v == 'max':
        continue
    events=dict(line.split() for line in (f.parent/'cgroup.events').read_text().splitlines())
    if events.get('populated') != '1':
        continue
    if f.parent.name.startswith('docker-'):
        external += int(v)
    else:
        other += int(v)
reserved=max(24*2**30,external)+other
print((reserved+2**30-1)//2**30)
RESERVATION
)
if [ $((reserved_gib+6)) -gt 50 ]; then echo "reservation hold: $reserved_gib GiB + 6 GiB exceeds 50"; exit 78; fi
echo "reservation: populated and external $reserved_gib GiB + 6 GiB"
M="$1"
RUN="${2:-a}"
SRC="$T/sources/$M.lean"
OUT="$T/objects/$M.olean"
TAG="$(printf '%s' "$M" | tr '/' '_')-$RUN"
mkdir -p "$(dirname "$OUT")"
# Never follow an inherited cached-output symlink during a compilation.
if [ -L "$OUT" ]; then unlink "$OUT"; fi
sha256sum "$SRC" > "$T/evidence/$TAG.sha256"
if systemd-run --user --scope --quiet -p MemoryHigh=4G -p MemoryMax=6G -p MemorySwapMax=0 -p TasksMax=128 /usr/bin/time -v -o "$T/evidence/$TAG.time.log" /usr/bin/timeout 900 python3 "$T/run2.py" "$T/environment-base.json" "$T/objects" "$T/sources" "$OUT" "$SRC" 5000 > "$T/evidence/$TAG.out.log" 2>&1; then STATUS=0; else STATUS=$?; fi
printf 'exit=%s\n' "$STATUS" >> "$T/evidence/$TAG.out.log"
python3 - "$T" "$M" "$RUN" "$STATUS" <<'PY'
import json,re,sys
from pathlib import Path
T=Path(sys.argv[1]); mod=sys.argv[2]; run=sys.argv[3]; code=int(sys.argv[4]); tag=mod.replace(chr(47),chr(95))+'-'+run
time=(T/'evidence'/f'{tag}.time.log').read_text()
def val(pattern):
 m=re.search(pattern,time,re.M); return m.group(1).strip() if m else None
r={"target":mod,"attempt":run,"exit_status":code,"source_sha256":(T/'evidence'/f'{tag}.sha256').read_text().split()[0],"elapsed_wall_clock":val(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)"),"max_rss_kib":val(r"Maximum resident set size \(kbytes\): (.+)"),"swaps":val(r"Swaps: (.+)"),"cgroup":{"MemoryHigh":"4G","MemoryMax":"6G","MemorySwapMax":"0","TasksMax":128},"lean_threshold_mb":5000,"log":f"{tag}.out.log","time_log":f"{tag}.time.log"}
(T/'evidence'/f'{tag}.receipt.json').write_text(json.dumps(r,indent=2)+'\n')
PY
cat "$T/evidence/$TAG.receipt.json"
tail -n 20 "$T/evidence/$TAG.out.log"
exit "$STATUS"
