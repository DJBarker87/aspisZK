from pathlib import Path
import subprocess,json,hashlib,re,time
P=Path(__file__).resolve().parent;HOST='dombarker@100.108.41.90';ROOT='/home/dombarker/project-offloads/aspis-joint-20261019';T='/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence';LAUNCH='/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/tools/run-joint.sh'
def ssh(cmd,data=None):return subprocess.run(['ssh',HOST,cmd],input=data,capture_output=True)
plan=json.loads((P/'checks.json').read_text());receipts=[];attempt=24300
for check in plan:
 s=(P/check['source']).read_bytes();mods=list(dict.fromkeys(m for m,n in check['items']))
 # Do not replace any imported source/object; bind focused checks to current cache.
 hashes=ssh('sha256sum '+' '.join(ROOT+'/sources/R1Z/'+m+'.lean '+ROOT+'/objects/R1Z/'+m+'.olean' for m in mods))
 (P/(check['module']+'-inputs.txt')).write_bytes(hashes.stdout+hashes.stderr)
 fp=hashlib.sha256(hashes.stdout).hexdigest()
 put=ssh('test ! -e '+ROOT+'/sources/'+check['module']+'.lean && cat > '+ROOT+'/sources/'+check['module']+'.lean',s)
 assert put.returncode==0,(check,put.stderr)
 for retry in range(11):
  a=attempt;attempt+=1;cmd=f'sh {LAUNCH} {a} {check["module"]} J 7000 8 {fp}'
  result=ssh(cmd);(P/f'launcher-{a}.log').write_bytes(result.stdout+result.stderr)
  raw=ssh(f'cat {T}/out-{a}.log');tim=ssh(f'cat {T}/time-{a}.log')
  (P/f'out-{a}.log').write_bytes(raw.stdout+raw.stderr);(P/f'time-{a}.log').write_bytes(tim.stdout+tim.stderr)
  compiler=b'Exit status:' in tim.stdout
  r=dict(attempt=a,module=check['module'],source_sha256=check['sha256'],source_revision='01304d43d6',dependency_fingerprint=fp,command=cmd,launcher_exit=result.returncode,compiler_invoked=compiler,limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=128,Lean_M=7000),log=f'out-{a}.log',time=f'time-{a}.log')
  receipts.append(r);(P/'receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
  print(a,check['module'],'compiler',compiler,'launcher',result.returncode,flush=True)
  refusal=b'RESERVATION HOLD' in result.stdout or b'allowed' in raw.stdout and b'False' in raw.stdout
  if refusal and not compiler:
   time.sleep(183);continue
  break
 else:print('Deferred after ten refusals',flush=True)
print('Complete',flush=True)
