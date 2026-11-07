from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
n=len(json.loads((E/'NNI_AUDIT_ROOTS.json').read_text())['groups']);modes=['batch'+str(i)for i in range(20)]+['batch20-21']+['batch'+str(i)for i in range(22,n)]
for i,mode in enumerate(modes,12):
 a=f'NNI_L{i:03}';p=E/a/'receipt.json'
 assert i<=57
 if p.exists():
  prior=json.loads(p.read_text());assert prior['module']==mode and prior['exit_status']==0
  print(a+' retained completed receipt; no replay',flush=True);continue
 r=subprocess.run([sys.executable,str(E/'NNI_run.py'),a,'audit',mode],capture_output=True,text=True);(E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 if r.returncode:
  good=True
  for j in range(int(mode[5:].split('-')[0]),int(mode[5:].split('-')[-1])+1):
   q=E/'NNI_audit'/mode/f'proof{j}.json'
   if not q.exists():good=False;break
   x=json.loads(q.read_text());expected=json.loads((E/'NNI_AUDIT_ROOTS.json').read_text())['groups'][j]
   good=good and [z['root']for z in x['results']]==expected and all(set(z['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}and(z['equal']or z['root']in {'NHC_DecodeModel.decoder_error','AspisR1.NKR_ScheduleExt.transition'})for z in x['results'])
  if not good:print(a+' STOP '+(r.stdout+r.stderr)[-1500:],flush=True);sys.exit(r.returncode)
  print(a+' '+mode+' raw standard; inherited collector finding retained',flush=True)
 else:print(a+' '+mode+' PASS',flush=True)
