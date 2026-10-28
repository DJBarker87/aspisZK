"""Remove only this lane's terminal-run solver temporaries."""
from pathlib import Path
import subprocess,json,sys,time
E=Path(__file__).resolve().parent;a=sys.argv[1]
r=json.loads((E/a/'receipt.json').read_text());assert r['exit_status']!=0
code='''from pathlib import Path
import json
p=Path('/home/dombarker/project-offloads/codex-cx-native-tx2m-20261028/NCD_tmp')
rows=[]
for q in p.rglob('*'):
 if q.is_file() and (q.name.startswith('external-sat') or q.name.startswith('smt2_dec_problem')):
  rows.append(dict(path=str(q),bytes=q.stat().st_size));q.unlink()
print(json.dumps(rows))
'''
for trial in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
 with (E/(a+'-cleanup-transport.jsonl')).open('a') as f:f.write(json.dumps(dict(trial=trial,exit=r.returncode,stdout=r.stdout,stderr=r.stderr))+'\n')
 if r.returncode==0:break
 if r.returncode!=255 or trial==10:raise SystemExit('STOP cleanup transport failure')
 time.sleep(60)
(E/(a+'-solver-cleanup.json')).write_text(r.stdout)
