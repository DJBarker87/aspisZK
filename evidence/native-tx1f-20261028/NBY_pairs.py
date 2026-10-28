"""Serial independent pairs; timeout defers its unchanged control only."""
from pathlib import Path
import sys,json,subprocess
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NBY_host as h
for number in range(int(sys.argv[1]),int(sys.argv[2])+1,2):
 if 80-len(list(E.glob('NBY_K[0-9][0-9][0-9]/receipt.json')))==1:raise SystemExit('One slot retained for imported arity negative control; no unpaired positive')
 for n in [number,number+1]:
  if len(list(E.glob('NBY_K[0-9][0-9][0-9]/receipt.json')))>=80:raise SystemExit('Kani budget exhausted; continue Lean-only work')
  a=f'NBY_K{n:03}';p=E/a/'receipt.json'
  if not p.exists():
   cfg=json.loads((E/(a+'.json')).read_text())
   if cfg.get('deferred'):print('DEFERRED',a,flush=True);break
   r=subprocess.run([sys.executable,str(E/'NBY_host.py'),a]);assert r.returncode==0
  rc=json.loads(p.read_text());out=(E/a/'stdout.log').read_text();cfg=json.loads((E/(a+'.json')).read_text())
  timed=any(x in out.lower() for x in ['cbmc timed out','harness timed out']) or rc['exit_status'] in [124,137]
  print('PAIR TERMINAL',a,rc['exit_status'],'timeout' if timed else '',flush=True)
  if timed:
   r=h.remote_py(f'''from pathlib import Path
import json
p=Path({(h.B+'/NBY_tmp')!r});out=[]
for x in p.rglob('*'):
 if x.is_file() and (x.name.startswith('external-sat') or x.name.startswith('smt2_dec_problem')):out.append(dict(path=str(x),size=x.stat().st_size));x.unlink()
print(json.dumps(out))''');assert r.returncode==0,r.stderr
   (E/(a+'-timeout-cleanup.json')).write_text(r.stdout)
   if n==number:
    cp=E/f'NBY_K{n+1:03}.json';c=json.loads(cp.read_text());c.update(deferred=True,reason=a+' timed out; unchanged matching shape not launched');cp.write_text(json.dumps(c,indent=2)+'\n')
   break
  if not cfg.get('expected_negative') and rc['exit_status']!=0:raise SystemExit('Positive finding / own input error; review this item')
  if cfg.get('expected_negative') and (rc['exit_status']==0 or 'VERIFICATION:- FAILED' not in out):raise SystemExit('Control finding; review this item')
