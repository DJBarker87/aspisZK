"""Retry one failed pre-submission transport step under local-lean rule 10."""
from pathlib import Path
import subprocess,time,json,datetime
E=Path(__file__).resolve().parent
cmd=['scp','-q','dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-cx-assoc-a4-cache-20261027/XSd_L025-barrier-0.log',str(E/'XSd_L025-barrier-0.log')]
for retry in range(1,11):
 time.sleep(60)
 start=time.time()
 try:
  r=subprocess.run(cmd,capture_output=True,text=True,timeout=30);rc=r.returncode;out=r.stdout+r.stderr
 except subprocess.TimeoutExpired as ex:
  rc=255;out='Transport timeout after 30 seconds; no compiler submitted.'
 event=dict(retry=retry,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),command=cmd,exit=rc,wall_seconds=time.time()-start,output=out,compiler_started=False)
 with (E/'XSd_transport_events.jsonl').open('a') as f:f.write(json.dumps(event)+'\n')
 print(json.dumps(event),flush=True)
 if rc==0:break
 if rc!=255:raise SystemExit(rc)
else:raise SystemExit('STOP: ten consecutive retry failures')
