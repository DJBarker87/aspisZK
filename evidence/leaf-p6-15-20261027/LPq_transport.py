"""Read-only, bounded pre-launch transport recovery; never submits a build."""
from pathlib import Path
import json, subprocess, time, datetime
E=Path(__file__).resolve().parent
p=E/'LPq_TRANSPORT.json'
rows=[dict(attempt=1,exit=255,stderr='Connection closed by 100.108.41.90 port 22',submitted=False),dict(attempt=2,exit=255,stderr='Connection timed out during banner exchange\nConnection to 100.108.41.90 port 22 timed out',submitted=False)]
p.write_text(json.dumps(rows,indent=2)+'\n')
for n in range(3,12):
    time.sleep(60)
    start=time.monotonic()
    r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','test -d /home/dombarker/project-offloads/codex-cx-sound-int2-20261025 && test -d /home/dombarker/project-offloads/codex-cx-assoc-a2-cache-20261027'],capture_output=True,text=True)
    row=dict(attempt=n,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),exit=r.returncode,wall_seconds=time.monotonic()-start,stdout=r.stdout,stderr=r.stderr,submitted=False)
    rows.append(row);p.write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(row),flush=True)
    if r.returncode==0:break
    if r.returncode!=255:raise SystemExit('STOP non-transient transport failure')
else:raise SystemExit('STOP initial failure plus ten failed recovery attempts; no process submitted')
