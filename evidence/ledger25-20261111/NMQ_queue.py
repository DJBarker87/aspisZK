from pathlib import Path
import subprocess,json,sys,time
E=Path(__file__).resolve().parent
jobs=[(2,'lean','NMQ_HypothesisReview'),(3,'lean','NMQ_Driver'),(4,'link','NMQ_Driver'),(5,'audit','fixtures'),(6,'lean','NMQ_OwnerStatements')]+[(7+i,'audit','batch'+str(i))for i in range(33)]
for i,kind,target in jobs:
 a=f'NMQ_L{i:03}';p=E/a/'receipt.json';assert not p.exists(),'Never replay completed '+a
 r=subprocess.run([sys.executable,str(E/'NMQ_run.py'),a,kind,target],capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 if r.returncode:
  if kind=='audit'and target.startswith('batch')and p.exists():
   result=E/'NMQ_audit'/target/('proof'+target[5:]+'.json')
   if not result.exists():print(a+' STOP missing batch receipt',flush=True);sys.exit(r.returncode)
   x=json.loads(result.read_text());group=json.loads((E/'NMQ_AUDIT_ROOTS.json').read_text())['groups'][int(target[5:])]
   allowed={'NHC_DecodeModel.decoder_error','AspisR1.NKR_ScheduleExt.transition'}
   assert [z['root']for z in x['results']]==group and all(set(z['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}and(z['equal']or z['root']in allowed)for z in x['results'])
   print(a+' raw standard; inherited collector finding retained',flush=True)
  else:print(a+' STOP '+(r.stdout+r.stderr)[-1200:],flush=True);sys.exit(r.returncode)
 else:print(a+' '+target+' PASS',flush=True)
