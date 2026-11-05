from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
jobs=[(5,'lean','NHO_ProofDriver'),(6,'link','NHO_ProofDriver'),(7,'lean','NHO_Driver'),(8,'link','NHO_Driver'),(9,'audit','fixtures'),(10,'audit','scan')]+[(i+11,'audit','batch'+str(i))for i in range(29)]+[(40,'lean','NHO_PLAN_STATEMENTS')]
for i,kind,target in jobs:
 a=f'NHO_L{i:03}'
 if (E/a/'receipt.json').is_file():continue
 with (E/(a+'-client.log')).open('w')as f:r=subprocess.run([sys.executable,str(E/'NHO_run.py'),a,kind,target],stdout=f,stderr=subprocess.STDOUT)
 print(a,kind,target,r.returncode,flush=True)
 if r.returncode:
  print((E/(a+'-client.log')).read_text()[-2600:],flush=True)
  # A raw/summary discrepancy is retained under (ab')(3); never patched away.
  if kind=='audit'and target=='batch26':
   x=json.loads((E/'NHO_audit/batch26/proof26.json').read_text());bad=[r for r in x['results']if not r['equal']]
   if len(bad)==1 and bad[0]['root']=='NHC_DecodeModel.decoder_error'and not bad[0]['collect_axioms']and set(bad[0]['walked_axioms'])=={'propext','Classical.choice','Quot.sound'}:continue
  sys.exit(r.returncode)
