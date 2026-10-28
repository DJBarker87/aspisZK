from pathlib import Path
import subprocess,json,sys,time,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdeac-20261028');label=sys.argv[1];script=sys.argv[2]
assert not (D/f'{label}-output.log').exists()
cool=D/'last-refusal.json'
if cool.exists():assert time.time()-json.loads(cool.read_text())['epoch']>=180,'cooldown active'
ad=D/f'admission-{label}.json'
with (D/f'admission-{label}.log').open('a') as f:p=subprocess.run(['python3',str(D.parent/'codex-pv-runjoin-20261026/reservation-existing.py'),str(ad)],stdout=f,stderr=subprocess.STDOUT)
if p.returncode!=0 or not ad.exists() or json.loads(ad.read_text()).get('allowed') is not True:
 (D/f'admission-{label}-refused-{int(time.time())}.json').write_bytes(ad.read_bytes() if ad.exists() else b'{}');cool.write_text(json.dumps(dict(epoch=time.time(),label=label,exit=p.returncode))+'\n');print('REFUSED',p.returncode);sys.exit(78)
cmd=['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',str(D/f'{label}-time.log'),'timeout','900','python3',str(D/script)]
with (D/f'{label}-output.log').open('w') as f:q=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
(D/f'{label}-receipt.json').write_text(json.dumps(dict(label=label,command=cmd,admission_exit=p.returncode,admission_allowed=True,exit=q.returncode,source_sha256=hashlib.sha256((D/script).read_bytes()).hexdigest(),revision=(D/'revision.txt').read_text().strip()),indent=2)+'\n')
print((D/f'{label}-output.log').read_text());print((D/f'{label}-time.log').read_text());sys.exit(q.returncode)
