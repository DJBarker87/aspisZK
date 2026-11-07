from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[('NNK_L002','lean','NNK_Driver'),('NNK_L003','link','NNK_Driver'),('NNK_L004','audit','fixtures')]
jobs += [(f'NNK_L{5+i:03}','audit','batch'+str(i))for i in range(48)]
for a,k,t in jobs:
 if (E/a/'receipt.json').exists():
  print(a,'retained; no resubmission',flush=True);continue
 with(E/(a+'-client.log')).open('w')as f:r=subprocess.run([sys.executable,str(E/'NNK_run.py'),a,k,t],stdout=f,stderr=subprocess.STDOUT)
 print(a,t,r.returncode,flush=True)
 if r.returncode:
  if k!='audit' or not t.startswith('batch'):sys.exit(r.returncode)
  d=json.loads((E/'NNK_audit'/t/('proof'+t[5:]+'.json')).read_text())
  expected=json.loads((E/'NNK_AUDIT_ROOTS.json').read_text())['groups'][int(t[5:])]
  assert [z['root']for z in d['results']]==expected
  assert all(set(z['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}and(z['equal']or z['root']in {'NHC_DecodeModel.decoder_error','AspisR1.NKR_ScheduleExt.transition','LIB_VCarriers.Acc'})for z in d['results'])
  print(a,'raw standard; retained collector disagreement',flush=True)
