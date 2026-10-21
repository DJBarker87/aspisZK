#!/usr/bin/env python3
import os,subprocess,concurrent.futures,time,json
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit14-20261021')
def lane(i,words):
 out=[]
 for word in words:
  env=dict(os.environ,PROVER_KANI_LANE=str(i))
  print('Starting bounded word case',word,'in lane',i,flush=True)
  rc=subprocess.run(['python3',str(H/'harness/kani.py'),f'm31-word{word}-v4',f'state_only_hiding::material14::word_{word}'],env=env).returncode
  print('Finished bounded word case',word,'exit',rc,flush=True)
  out.append(dict(word=word,exit_status=rc))
  if rc:break
 return out
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
 jobs=[pool.submit(lane,i,words) for i,words in enumerate([[0,3,6],[1,4,7],[2,5]])]
 while not all(j.done() for j in jobs):
  concurrent.futures.wait(jobs,timeout=45)
  print('Heartbeat: completed lanes',sum(j.done() for j in jobs),'of 3',flush=True)
 rows=[r for j in jobs for r in j.result()]
(H/'word-split-results.json').write_text(json.dumps(rows,indent=2)+'\n')
raise SystemExit(0 if len(rows)==8 and all(r['exit_status']==0 for r in rows) else 1)
