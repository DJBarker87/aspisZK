from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for n,mode,indices in [(47,'split41a',[41]),(48,'split41b',[48]),(49,'batch42-43',[42,43]),(50,'batch44',[44]),(51,'batch45',[45]),(52,'batch46',[46]),(53,'batch47',[47])]:
 a=f'NNK_L{n:03}';assert not(E/a).exists()
 with(E/(a+'-client.log')).open('w')as f:r=subprocess.run([sys.executable,str(E/'NNK_run.py'),a,'audit',mode],stdout=f,stderr=subprocess.STDOUT)
 print(a,mode,r.returncode,flush=True)
 if r.returncode:
  for i in indices:
   d=json.loads((E/'NNK_audit'/mode/('proof'+str(i)+'.json')).read_text());expected=json.loads((E/'NNK_AUDIT_ROOTS.json').read_text())['groups'][i]
   assert [z['root']for z in d['results']]==expected
   assert all(set(z['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}and(z['equal']or z['root']in {'NHC_DecodeModel.decoder_error','AspisR1.NKR_ScheduleExt.transition','LIB_VCarriers.Acc'})for z in d['results'])
