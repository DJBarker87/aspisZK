"""Serial diagnostic scopes after the unmodified full import failed."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
jobs=[(4,'lean','NII_ProofDriver'),(5,'link','NII_ProofDriver'),(6,'lean','NII_Driver'),(7,'link','NII_Driver'),(8,'audit','fixtures'),(9,'audit','scan')]+[(10+i,'audit','batch'+str(i))for i in range(30)]+[(40,'lean','NII_PLAN_STATEMENTS')]
for i,kind,target in jobs:
 a=f'NII_L{i:03}'
 if (E/a/'receipt.json').is_file():continue
 with (E/(a+'-client.log')).open('w')as f:r=subprocess.run([sys.executable,str(E/'NII_run.py'),a,kind,target],stdout=f,stderr=subprocess.STDOUT)
 print(a,kind,target,r.returncode,flush=True)
 if r.returncode:
  if kind=='audit' and target.startswith('batch'):
   x=json.loads((E/'NII_audit'/target/('proof'+target[5:]+'.json')).read_text());bad=[v for v in x['results']if not v['equal']]
   if len(bad)==1 and bad[0]['root']=='NHC_DecodeModel.decoder_error'and not bad[0]['collect_axioms']and set(bad[0]['walked_axioms'])=={'propext','Classical.choice','Quot.sound'}:continue
  print((E/(a+'-client.log')).read_text()[-2200:],flush=True);sys.exit(r.returncode)
