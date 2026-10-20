from pathlib import Path
import os,sys,json,hashlib,subprocess,time,datetime
packet=Path(__file__).resolve().parent; root=packet.parents[1]; repo=root.parents[2]
module=sys.argv[1]; src=root/'lean'/f'{module}.lean'; obj=Path('/tmp/codex-cx-overflow-s2-20261020-objects'); obj.mkdir(exist_ok=True)
base=json.loads((root/'evidence/stage2-continuation-20261020/proofs/parse-v3/command.json').read_text())
leanpath=str(obj)+':/tmp/r1-overflow-free-20261019-objects:'+base['lean_path']
lock=Path('/tmp/aspis-local-lean.lock.d')
while True:
 try: lock.mkdir(); break
 except FileExistsError: time.sleep(15)
try:
 while True:
  pids=subprocess.run(['pgrep','-x','lean'],capture_output=True,text=True).stdout.split()
  ps=subprocess.run(['ps','-p',','.join(pids),'-o','args='],capture_output=True,text=True).stdout if pids else ''
  if '-M4400' not in ps: break
  time.sleep(30)
 digest=hashlib.sha256(src.read_bytes()).hexdigest(); stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
 dest=packet/'receipts'/f'{module}-{stamp}'; dest.mkdir(parents=True)
 cmd=[base['command'][0],'-j1','-M4400','-DElab.async=false','-o',str(obj/f'{module}.olean'),str(src)]
 imports=[]
 for line in src.read_text().splitlines():
  if not line.startswith('import '): continue
  name=line.split()[1]; rel=name.replace('.','/')+'.olean'
  p=next((Path(x)/rel for x in leanpath.split(':') if (Path(x)/rel).exists()),None)
  imports.append({'module':name,'object':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest() if p else None})
 fp=hashlib.sha256(json.dumps(imports,sort_keys=True).encode()).hexdigest()
 for old in (packet/'receipts').glob('*/receipt.json'):
  r=json.loads(old.read_text())
  if r['module']==module and r['source_sha256']==digest and r['deps_fingerprint']==fp: raise SystemExit('Unchanged attempt refused')
 start=time.monotonic()
 with (dest/'out.log').open('w') as log,(dest/'time.log').open('w') as tm:
  p=subprocess.run(['/usr/bin/time','-l']+cmd,stdout=log,stderr=tm,env={**os.environ,'LEAN_PATH':leanpath},cwd=repo)
 elapsed=time.monotonic()-start
 output=(dest/'out.log').read_text(); metrics=(dest/'time.log').read_text()
 r={'schema':'focused-extractor-proof-packet-v1','module':module,'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),'source_sha256':digest,'deps_fingerprint':fp,'imports':imports,'command':cmd,'lean_path':leanpath,'exit':p.returncode,'wall_seconds':elapsed,'axioms':[l for l in output.splitlines() if 'depends on axioms' in l or 'does not depend on any axioms' in l],'time_log':metrics,'source_unchanged':hashlib.sha256(src.read_bytes()).hexdigest()==digest}
 (dest/'receipt.json').write_text(json.dumps(r,indent=2)+'\n')
 receipts=[json.loads(f.read_text()) for f in sorted((packet/'receipts').glob('*/receipt.json'))]
 (packet/'manifest.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','attempts':receipts},indent=2)+'\n')
 print(str(dest)); print(output); print(metrics); sys.exit(p.returncode)
finally:
 try: lock.rmdir()
 except OSError as e: print('Lock release could not remove shared directory:', e)
