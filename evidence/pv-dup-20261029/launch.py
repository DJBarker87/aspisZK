"""One admitted read-only inspection at a time. Objects are inputs only."""
from pathlib import Path
import json,hashlib,subprocess,sys,time,os
B=Path(__file__).resolve().parent;os.chdir(B)
a=int(sys.argv[1]);mode=sys.argv[2];assert 70750<=a<=70796
cfg=json.load(open(f'attempt-{a}.json'))
assert not (B/cfg['attempt']).exists()
# Failed proof/elaboration source cannot be resubmitted unchanged.
for p in B.glob('lean-*/receipt.json'):
 old=json.load(open(p))
 if old['exit_status']!=0:
  for f in cfg['sources']:
   assert hashlib.sha256(Path(f).read_bytes()).hexdigest() not in old['source_hashes'].values(),('unchanged failed source',f)
for n in range(11):
 out=B/f'admission-{a}-{n}.json'
 with open(f'admission-{a}-{n}.log','w') as log:
  r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-pv-runjoin-20261026/reservation-existing.py',str(out)],stdout=log,stderr=subprocess.STDOUT)
 d=json.load(open(out)) if out.exists() else None
 Path(f'admission-exit-{a}-{n}.json').write_text(json.dumps({'exit':r.returncode,'allowed':d.get('allowed') if d else None,'epoch':time.time()}))
 if r.returncode==0 and d and d.get('allowed') is True:break
 if r.returncode==78 or d and d.get('allowed') is False:
  print('REFUSED',a,n,flush=True)
  if n==10:sys.exit(78)
  time.sleep(180);continue
 sys.exit('reservation infrastructure failure')
command=['systemd-run','--user','--scope','--quiet',f'--unit=pv-dup-{a}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3','S2W_run_host.py',f'attempt-{a}.json']
print('START',a,mode,flush=True)
sys.exit(subprocess.run(command).returncode)
