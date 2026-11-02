from pathlib import Path
import subprocess,json,hashlib,sys,time
B=Path(__file__).resolve().parent
O=B.parent/'codex-pv-bridge-20261101'
a=int(sys.argv[1]);assert a in [90000,90001]
assert json.load(open(B/'verification.json'))['status']=='PASS'
cfg=json.load(open(B/f'attempt-{a}.json'));assert not (B/cfg['attempt']).exists()
for f in cfg['sources']:
 h=hashlib.sha256((B/f).read_bytes()).hexdigest()
 if a==90000:assert h=='48381d7a82300eadec1f5973cd87bd5b4119d1f399717d9210263e379ef1297e'
 for d in [B,O]:
  for p in d.glob('lean-*/receipt.json'):
   old=json.load(open(p));assert not(old.get('exit_status',0)!=0 and h in old.get('source_hashes',{}).values()),('unchanged failed source',str(p))
if a==90000:assert not (O/'objects/PV_BR_FixtureConsumer.olean').exists(),'target object already exists'
else:assert json.load(open(B/'lean-90000/receipt.json'))['exit_status']==0
pins={'reservation_agg16.py':'d6d40da5e7cad196b15974eb96526f28073d20b2c24855303d69bc605ebcac0f','S2W_lean_host_agg16.py':'9b325ab05e4aea7c8a2c3499ccef5de11898fdcba38cb803fc6a85111ca3f1dd','S2W_run_host_agg16.py':'8165ccff93f7d9b6043f55bf641c30c95c5af0f86d28b6e1b1ffef3aa5ea7ff6'}
for f,h in pins.items():assert hashlib.sha256((B/f).read_bytes()).hexdigest()==h
for n in range(20):
 p=B/f'admission-{a}-{n}.json'
 with (B/f'admission-{a}-{n}.log').open('w') as log:
  r=subprocess.run(['python3',str(B/'reservation_agg16.py'),str(p)],stdout=log,stderr=subprocess.STDOUT)
 d=json.load(open(p)) if p.exists() else {}
 (B/f'admission-exit-{a}-{n}.json').write_text(json.dumps({'exit':r.returncode,'allowed':d.get('allowed'),'epoch':time.time()})+'\n')
 if r.returncode==0 and d.get('allowed') is True:break
 if r.returncode==78 or d.get('allowed') is False:
  print('REFUSED',a,n,flush=True)
  if n==19:sys.exit(78)
  time.sleep(180);continue
 sys.exit('reservation infrastructure failure')
print('START',a,flush=True)
cmd=['systemd-run','--user','--scope',f'--unit=pv-bridge-agg-{a}','-p','MemoryHigh=14G','-p','MemoryMax=16G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(B/'S2W_lean_host_agg16.py'),f'attempt-{a}.json']
sys.exit(subprocess.run(cmd,cwd=B).returncode)
