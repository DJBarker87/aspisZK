"""Own serial facet runner; 99 remaining Kani attempts, stop on unexpected verdict."""
from pathlib import Path
import subprocess,sys,os,json
E=Path(__file__).resolve().parent;rows=json.loads((E/'NIY_NATIVE_MATRIX.json').read_text())
start=int(sys.argv[1]) if len(sys.argv)>1 else 2
familystart=int(sys.argv[2]) if len(sys.argv)>2 else 0
limit=int(sys.argv[3]) if len(sys.argv)>3 else len(rows)
a=start
for row in rows[familystart:limit]:
 for mode in ['positive','negative','rename']:
  if a>100:
   (E/'NIY_KANI_BUDGET_END.json').write_text(json.dumps(dict(next_attempt=a,family=row['family'],mode=mode,budget=100)))
   sys.exit(0)
  env=dict(os.environ)
  if mode=='negative':env['NIY_INVERT']='1'
  target=row['rename'] if mode=='rename' else row['function'];attempt=f'NIY_K{a:03d}'
  p=subprocess.run([sys.executable,str(E/'NIY_run.py'),attempt,'kani',target],env=env)
  row[mode]=attempt;a+=1
  r=json.loads((E/attempt/'receipt.json').read_text());raw=(E/attempt/'stdout.log').read_text()
  terminal_limit=any(t in raw.lower() for t in ['timed out','timeout','out of memory','excessive memory'])
  semantic_fail=('VERIFICATION:- FAILED' in raw or 'VERIFICATION: FAILED' in raw) and not terminal_limit
  semantic_pass='VERIFICATION:- SUCCESSFUL' in raw or 'VERIFICATION: SUCCESSFUL' in raw
  ok=(r['exit_status']!=0 and semantic_fail) if mode=='negative' else (r['exit_status']==0 and semantic_pass)
  row[mode+'_qualified']=ok
  row['status']='qualified local facet; not parent' if all(row.get(x+'_qualified') for x in ['positive','negative','rename']) else 'partial'
  (E/'NIY_NATIVE_MATRIX.json').write_text(json.dumps(rows,indent=2)+'\n')
  if not ok:
   row['status']='unexpected verdict; isolate before next launch';(E/'NIY_NATIVE_MATRIX.json').write_text(json.dumps(rows,indent=2)+'\n');sys.exit(1)
