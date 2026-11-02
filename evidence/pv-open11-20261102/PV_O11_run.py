from pathlib import Path
import sys,subprocess,json,hashlib,time,os,re
D=Path('/home/dombarker/project-offloads/codex-pv-open11-20261102'); mode=sys.argv[1];a=sys.argv[2]
assert (mode=='lean' and 90400<=int(a)<=90499) or (mode in ('native','extract') and 90500<=int(a)<=90529)
R=D/('N'+a if mode in ('native','extract') else a);R.mkdir(exist_ok=True)
assert not (R/'receipt.json').exists(),'attempt used'
last=D/'last-refusal.json'
if last.exists():assert time.time()-json.loads(last.read_text())['epoch']>=180,'cooldown'
ad=R/'admission.json'
with (R/'admission.log').open('a') as f:p=subprocess.run(['python3',str(D/'PV_O11_reservation.py'),str(ad)],stdout=f,stderr=subprocess.STDOUT)
if p.returncode or not ad.exists() or json.loads(ad.read_text()).get('allowed') is not True:
 last.write_text(json.dumps(dict(epoch=time.time(),id=a,exit=p.returncode)));print('REFUSED',p.returncode);sys.exit(78)
source=D/('lean/PV_O11_KindView.lean' if mode=='lean' else 'extract/lib.rs' if mode=='extract' else 'PV_O11_kind_native.rs')
sha=hashlib.sha256(source.read_bytes()).hexdigest()
for rec in D.glob('*/receipt.json'):
 old=json.loads(rec.read_text());assert not(old.get('exit')!=0 and old.get('source_sha256')==sha),'unchanged FAILED source guard'
if mode=='lean':
 manifest=json.loads((D/'inputs/external-object-manifest.json').read_text());checks=[]
 for x in manifest:
  p=Path(x['path']);h=hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None
  checks.append(dict(module=x['module'],path=str(p),expected=x['object_sha256'],actual=h,ok=h==x['object_sha256']))
 (R/'external-check.json').write_text(json.dumps(checks,indent=2)+'\n')
 # Init-only target: any mismatch in any object in authority is recorded;
 # hard stop for toolchain Init/Lean which this target can load.
 assert all(x['ok'] for x in checks if x['module'].startswith(('Init/','Lean/')) or x['module'] in ['Init','Lean']), 'external authority mismatch'
 env=json.loads((D/'inputs/env-J.json').read_text());env['LEAN_PATH']=str(D/'objects')+':'+env['LEAN_SYSROOT']+'/lib/lean';(D/'env.json').write_text(json.dumps(env))
 (D/'objects').mkdir(exist_ok=True)
 cmd=['python3',str(D.parent/'aspis-fs-generic-20261006/evidence/run2.py'),str(D/'env.json'),str(D/'objects'),str(D/'lean'),str(D/'objects/PV_O11_KindView.olean'),str(source),'7000']
else:
 cmd=['python3',str(D/('PV_O11_extract.py' if mode=='extract' else 'PV_O11_native.py'))]
limits=['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64']
cmd=limits+['/usr/bin/time','-v','-o',str(R/'time.log'),'timeout','900']+cmd
start=time.time()
with (R/'output.log').open('w') as f:p=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
log=(R/'output.log').read_text();t=(R/'time.log').read_text()
r=dict(attempt=a,mode=mode,target=str(source),source_sha256=sha,revision=(D/'revision.txt').read_text().strip(),exit=p.returncode,wall_seconds=time.time()-start,command=cmd,print_axioms=re.findall(r".*depends on axioms.*",log) if mode=='lean' else 'N/A native finite validation',axioms_class='SUMMARY-BASED' if mode=='lean' else None,peak_rss_kib=re.search(r'Maximum resident set size \(kbytes\): (\d+)',t).group(1),swaps=re.search(r'Swaps: (\d+)',t).group(1),admission_exit=0,admission_allowed=True,failed_source_guard_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
(R/'receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(log);print(json.dumps(r));sys.exit(p.returncode)
