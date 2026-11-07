"""Serial own client; raw collector findings do not suppress raw standard-axiom checks."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
jobs=[(2,'lean','NLX_Driver'),(3,'lean','NLX_ProofDriver'),(4,'link','NLX_Driver'),(5,'link','NLX_ProofDriver'),(6,'audit','fixtures'),(7,'audit','scan'),(8,'lean','NLX_OwnerStatements')]+[(9+i,'audit','batch'+str(i))for i in range(30)]
for i,kind,target in jobs:
 a=f'NLX_L{i:03}';p=E/a/'receipt.json'
 if p.exists():raise RuntimeError('Never replay completed '+a)
 r=subprocess.run([sys.executable,str(E/'NLX_run.py'),a,kind,target],capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 if r.returncode:
  if kind=='audit'and target.startswith('batch')and p.exists():
   x=json.loads((E/'NLX_audit'/target/('proof'+target[5:]+'.json')).read_text())
   group=json.loads((E/'NLX_AUDIT_ROOTS.json').read_text())['groups'][int(target[5:])]
   allowed={'NHC_DecodeModel.decoder_error','AspisR1.NKR_ScheduleExt.transition'}
   assert [z['root']for z in x['results']]==group and all(set(z['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}and(z['equal']or z['root']in allowed)for z in x['results'])
   print(a+' raw standard; inherited collector finding retained',flush=True)
  else:print(a+' STOP '+(r.stdout+r.stderr)[-800:],flush=True);sys.exit(r.returncode)
 else:print(a+' '+target+' PASS',flush=True)
