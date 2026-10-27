"""Serial adoption gates. Stop on any comparison disagreement; never time."""
from pathlib import Path
import subprocess,json,shlex,time,sys
D='/home/dombarker/project-offloads/codex-pv-integ1-20261027';H='dombarker@100.108.41.90';E=Path('evidence/pv-integ1-20261027')
def call(script,args,label):
 for retry in range(10):
  actual=label if retry==0 else label+f'-reservation-{retry+1:02}'
  argv=['python3',D+'/'+script,*[actual if x=='{label}' else x for x in args]]
  with (E/(actual+'-driver.log')).open('w') as out:
   r=subprocess.run(['ssh',H,shlex.join(argv)],stdout=out,stderr=subprocess.STDOUT)
  if r.returncode:
   raw=subprocess.run(['ssh',H,'cat '+D+'/'+actual+'/admission-barrier.json'],capture_output=True,text=True)
   if raw.returncode==0 and not json.loads(raw.stdout)['allowed']:
    (E/(actual+'-barrier-refusal.json')).write_text(json.dumps(dict(raw_exit=r.returncode,classification='reservation refusal; no native command ran',admission=json.loads(raw.stdout)),indent=2)+'\n')
    r.returncode=78
  print(label,actual,'exit',r.returncode,flush=True)
  if r.returncode==78:
   for _ in range(3):print('reservation cooldown: 60 seconds',flush=True);time.sleep(60)
   continue
  if r.returncode:raise SystemExit(r.returncode)
  return actual
 raise SystemExit(78)

if __name__=='__main__':
 labels={}
 for mode in ['default','devnet','pool']:
  labels[mode]=call('build.py',['candidate',mode,'{label}'],'build-'+mode+'-executable-wrapper')
  r=json.loads(subprocess.check_output(['ssh',H,'cat '+D+'/'+labels[mode]+'/comparison.json'],text=True));assert r['matches'],r
 (E/'elf-labels.json').write_text(json.dumps(labels,indent=2)+'\n')
