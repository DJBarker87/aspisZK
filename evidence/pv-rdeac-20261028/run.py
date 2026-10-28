from pathlib import Path
import subprocess,json,sys,time,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdeac-20261028')
a=int(sys.argv[1]);m=sys.argv[2];assert 61100<=a<=61199
P=D.parent/'codex-pv-rdea-20261028';out=D/f'out-{a}.log';assert not out.exists(),a
cool=D/'last-refusal.json'
if cool.exists():assert time.time()-json.loads(cool.read_text())['epoch']>=180,'cooldown active'
ad=D/f'admission-{a}.json'
with (D/f'admission-{a}.log').open('a') as f:
 p=subprocess.run(['python3',str(D.parent/'codex-pv-runjoin-20261026/reservation-existing.py'),str(ad)],stdout=f,stderr=subprocess.STDOUT)
if p.returncode!=0 or not ad.exists() or json.loads(ad.read_text()).get('allowed') is not True:
 (D/f'admission-{a}-refused-{int(time.time())}.json').write_bytes(ad.read_bytes() if ad.exists() else b'{}');cool.write_text(json.dumps(dict(epoch=time.time(),id=a,exit=p.returncode))+'\n');print('REFUSED',p.returncode);sys.exit(78)
source=D/'sources'/(m.replace('.','/')+'.lean');obj=D/'objects'/(m.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
assert source.exists()
snapshot=D/'attempt-sources'/f'{a}.lean';snapshot.parent.mkdir(exist_ok=True);snapshot.write_bytes(source.read_bytes())
cmd=['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/time','-v','-o',str(D/f'time-{a}.log'),'timeout','900','python3',str(D.parent/'aspis-fs-generic-20261006/evidence/run2.py'),str(D/'env-J.json'),str(D/'objects'),str(D/'sources'),str(obj),str(source),'7000']
receipt=dict(attempt=a,target=m,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),command=cmd,admission_exit=p.returncode,admission_allowed=True,revision=(D/'revision.txt').read_text().strip())
with out.open('w') as f:p=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
receipt.update(exit=p.returncode,object_sha256=hashlib.sha256(obj.read_bytes()).hexdigest() if p.returncode==0 else None)
(D/f'receipt-{a}.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(out.read_text());print((D/f'time-{a}.log').read_text());sys.exit(p.returncode)
