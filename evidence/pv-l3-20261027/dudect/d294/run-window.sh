#!/bin/bash
set -u
B=/home/dombarker/project-offloads/codex-pv-dudect-20261027
R=$B/d294
mkdir -p "$R"
cleanup() {
  python3 - "$R" <<'PY'
import pathlib,json,time,sys
q=pathlib.Path('/home/dombarker/project-offloads/QUIET_WINDOW.json');r=pathlib.Path(sys.argv[1])
if (r/'marker-created.json').exists():
 expected=json.loads((r/'marker-created.json').read_text())['marker']
 actual=json.loads(q.read_text()) if q.exists() else None
 if actual==expected:q.unlink()
 (r/'marker-removal.json').write_text(json.dumps(dict(epoch=time.time(),actual=actual,removed=actual==expected,absent=not q.exists()),indent=2)+'\n')
PY
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
python3 - "$R" <<'PY'
import pathlib,json,time,sys,hashlib
b=pathlib.Path('/home/dombarker/project-offloads/codex-pv-dudect-20261027');r=pathlib.Path(sys.argv[1]);q=b.parent/'QUIET_WINDOW.json'
pins={'pv-dudect':'ede68055604cce057f3d0b96fa575b06f30290bba4bcdb50493b7b81a797eb02','devnet_spend':'161abfd8d155a2ccf35a461cd8e03fbf909e0f8b1c59efdddec1d76e74811472'}
actual={n:hashlib.sha256((b/'bin'/n).read_bytes()).hexdigest() for n in pins};assert actual==pins
now=time.time();m=dict(until=now+1500,owner='stream-b-pv-dudect',purpose='V374 dudect')
with q.open('x') as f:json.dump(m,f);f.write('\n')
(r/'marker-created.json').write_text(json.dumps(dict(epoch=now,marker=m,binary_sha256=actual),indent=2)+'\n')
print(json.dumps(dict(marker_created=now,until=m['until'])),flush=True)
PY
rc=$?
if [ "$rc" -ne 0 ]; then exit "$rc"; fi
python3 - "$R" <<'PY'
import pathlib,json,time,sys,subprocess
r=pathlib.Path(sys.argv[1]);start=time.monotonic();deadline=start+300
with (r/'drain.jsonl').open('x') as log:
 while True:
  active=[]
  for f in pathlib.Path('/sys/fs/cgroup/user.slice').rglob('memory.max'):
   p=f.parent
   try:
    if 'populated 1' not in (p/'cgroup.events').read_text():continue
    if f.read_text().strip()=='max' and not any(x.startswith(('cx-','pv-')) for x in p.parts):continue
    procs=[]
    for pid in (p/'cgroup.procs').read_text().split():
     try:procs.append(dict(pid=int(pid),cmd=pathlib.Path('/proc',pid,'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')))
     except FileNotFoundError:pass
    active.append(dict(path=str(p),memory_max=f.read_text().strip(),processes=procs))
   except FileNotFoundError:continue
  row=dict(epoch=time.time(),elapsed=time.monotonic()-start,active=active)
  log.write(json.dumps(row)+'\n');log.flush();print(json.dumps(row),flush=True)
  if not active:break
  if time.monotonic()>=deadline:
   (r/'abort.json').write_text(json.dumps(dict(reason='5-minute drain timeout',**row),indent=2)+'\n');sys.exit(78)
  time.sleep(min(30,max(0,deadline-time.monotonic())))
PY
rc=$?
if [ "$rc" -ne 0 ]; then exit "$rc"; fi
python3 - "$R" <<'COOL'
import sys,pathlib,json,time
r=pathlib.Path(sys.argv[1]);sys.path.insert(0,str(r))
from thermal_monitor import snapshot,excluded
q=r.parent.parent/'QUIET_WINDOW.json'
marker=json.loads((r/'marker-created.json').read_text())['marker']
start=time.monotonic();deadline=start+300
with (r/'cooldown.jsonl').open('x') as log:
 while True:
  assert json.loads(q.read_text())==marker and time.time()<marker['until'], 'marker changed or expired'
  row=dict(elapsed=time.monotonic()-start,**snapshot());log.write(json.dumps(row)+'\n');log.flush();print(json.dumps(row),flush=True)
  if row['package_c']<80:break
  if time.monotonic()>=deadline:
   (r/'abort.json').write_text(json.dumps(dict(reason='package did not cool below 80 C within 5 minutes',**row),indent=2)+'\n');sys.exit(78)
  time.sleep(min(10,max(0,deadline-time.monotonic())))
COOL
rc=$?
if [ "$rc" -ne 0 ]; then exit "$rc"; fi
cd "$B/src" || exit 1
QUIET_WINDOW_OWNER=1 python3 "$R/window_v21.py" --execute-lead-window > "$R/entrypoint.log" 2>&1
rc=$?
printf '%s\n' "$rc" > "$R/entrypoint.exit"
exit "$rc"
