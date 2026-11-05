"""Read-only recovery of own export artifacts; no prover submission."""
from pathlib import Path
import subprocess,time,json
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-experiment-law-20261106'
ad=json.loads((E/'NHZ_L023-admission.json').read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
for name in ['NHZ_CLOSURE_PINS.json.xz','NHZ_CLOSURE_PINS.json.sha256','NHZ_EXPORT.json','NHZ_RESTORE_PATHS.json','NHZ_TOOLS.json']:
 for retry in range(11):
  r=subprocess.run(['scp','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90:'+B+'/'+name,str(E/name)],capture_output=True,text=True)
  with (E/'NHZ_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(stage='fetch',name=name,retry=retry,exit=r.returncode,stderr=r.stderr))+'\n')
  if r.returncode!=255:break
  if retry<10:time.sleep(60)
 assert r.returncode==0,r.stderr
print('Fetched own export artifacts')
