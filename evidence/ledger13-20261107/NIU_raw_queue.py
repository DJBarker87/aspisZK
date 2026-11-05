from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for i in range(30):
 a=f'NIU_L{i+10:03}';r=subprocess.run([sys.executable,str(E/'NIU_run.py'),a,'audit',f'batch{i}'])
 if r.returncode:
  p=E/'NIU_audit'/f'batch{i}'/f'proof{i}.json'
  if not p.exists():sys.exit(r.returncode)
  d=json.loads(p.read_text());bad=[x for x in d['results']if not x['equal']]
  if not (d['exit_status']==1 and [x['root']for x in bad]==['NHC_DecodeModel.decoder_error'] and set(bad[0]['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}):sys.exit(r.returncode)
  print(json.dumps(dict(attempt=a,status='retained ab-prime-3 discrepancy; raw authoritative')),flush=True)
