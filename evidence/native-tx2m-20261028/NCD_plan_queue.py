"""Own sequential proof queue; no retries of proof outcomes."""
from pathlib import Path
import json,subprocess,sys,hashlib
E=Path(__file__).resolve().parent
rows=json.loads(Path(sys.argv[1]).read_text());start=int(sys.argv[2]);state={}
for p in sorted(E.glob('NCD_L*/receipt.json')):
 r=json.loads(p.read_text());m=r['module'];src=Path('lean')/(m+'.lean')
 state[m]=r['exit_status']==0 and src.exists() and hashlib.sha256(src.read_bytes()).hexdigest() in r['source_hashes'].values()
for i,row in enumerate(rows,start):
 m=row['module'];a=f'NCD_L{i:03d}'
 if state.get(m):print('REUSE',m,flush=True);continue
 if any(d.startswith('NCD_') and not state.get(d) for d in row.get('imports',[])):
  state[m]=False;print('BLOCKED predecessor',m,flush=True);continue
 if (E/(a+'.json')).exists():raise SystemExit('Recover existing attempt '+a)
 r=subprocess.run([sys.executable,str(E/'NCD_build.py'),a,row['path'],m],capture_output=True,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json'
 if not p.exists():print('STOP missing receipt',a,r.stdout+r.stderr,flush=True);break
 rc=json.loads(p.read_text());state[m]=rc['exit_status']==0
 print(a,m,rc['exit_status'],rc['wall_seconds'],flush=True)
 if not state[m]:print((E/a/'stdout.log').read_text()[-4500:],flush=True)
(E/'NCD_PLAN_STATE.json').write_text(json.dumps(state,indent=2)+'\n')
