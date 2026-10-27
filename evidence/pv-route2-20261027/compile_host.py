from pathlib import Path
import subprocess,hashlib,json,time,sys,re
D=Path('/home/dombarker/project-offloads/codex-pv-route2-20261027');J=Path('/home/dombarker/project-offloads/aspis-joint-20261019');T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence');L='/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/tools/run-joint.sh'
rows=json.loads((D/'split.json').read_text());nextid=int(sys.argv[1]);budget=int(sys.argv[2]);done=[]
for row in rows:
 if len(done)>=budget:break
 module=row['module'];src=D/'lean'/(module+'.lean');dst=J/'sources'/(module+'.lean');assert not dst.exists(),str(dst);dst.write_bytes(src.read_bytes())
 deps={}
 for imp in re.findall(r'^import (\S+)',src.read_text(),re.M):
  search=[str(J/'objects')]+json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text())['LEAN_PATH'].split(':')
  p=next((Path(root)/(imp.replace('.','/')+'.olean') for root in search if (Path(root)/(imp.replace('.','/')+'.olean')).exists()),J/'objects'/(imp+'.olean'))
  if p.exists():deps[imp]=hashlib.sha256(p.read_bytes()).hexdigest()
  else:deps[imp]='missing'
 fp=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest();a=nextid;nextid+=1;O=D/'lean-receipts'/str(a);O.mkdir(parents=True)
 submission=dict(attempt=a,module=module,source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),dependency_object_hashes=deps,deps_fingerprint=fp,source_revision=(D/'revision').read_text().strip());(O/'submission.json').write_text(json.dumps(submission,indent=2));start=time.monotonic()
 r=subprocess.run([L,str(a),module,'J','7000','8',fp],stdout=open(O/'launcher.log','w'),stderr=subprocess.STDOUT)
 out=(T/f'out-{a}.log');tm=T/f'time-{a}.log';txt=out.read_text() if out.exists() else '';wall=time.monotonic()-start
 for origin,name in [(out,'out.log'),(tm,'time.log')]:
  if origin.exists():(O/name).write_bytes(origin.read_bytes())
 status=re.findall(r'^exit=(\d+)',txt,re.M);status=int(status[-1]) if status else r.returncode
 receipt=dict(**submission,launcher_exit=r.returncode,exit=status,wall_seconds=wall,print_axioms=re.findall(r"^.*(?:depends on axioms|does not depend on any axioms).*$",txt,re.M),time_log=tm.read_text() if tm.exists() else None)
 (O/'receipt.json').write_text(json.dumps(receipt,indent=2));print(a,module,status,flush=True)
 if not out.exists(): print('launch refusal: review before next scope',flush=True);break
 done.append(receipt);(D/'TALLY.json').write_text(json.dumps(dict(lean_attempts=len(done),budget=60,next_unused_id=nextid,kani=0,receipts=done),indent=2))
 if status:print(txt[-3500:],flush=True);break
