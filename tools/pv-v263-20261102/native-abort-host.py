from pathlib import Path
import subprocess,hashlib,json,time,sys,resource,signal,re
p=Path(sys.argv[1]);tag='N90122';src=p/'tools/pv-v263-20261102/native-abort.rs';out=p/'native-abort';results=[]
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
cmd=['/home/dombarker/.cargo/bin/rustc','+1.94.1','--edition=2021','-C','opt-level=3','-C','debug-assertions=no','-C','overflow-checks=no','-C','panic=abort',str(src),'-o',str(out)]
for target,command in [('compile-abort-profile',cmd),('nested-tls-and-inner-results-abort-profile',[str(out),'success']),('spawn-denial-aborts-before-callback',[str(out),'failure'])]:
 start=time.monotonic();q=subprocess.run(command,text=True,capture_output=True,timeout=60)
 expected=(q.returncode==-signal.SIGABRT and 'CALLBACK-EXECUTED' not in q.stderr and 'UNEXPECTED-RETURN' not in q.stdout and 'failed to spawn thread' in q.stderr and re.search(r'occupied=[1-9][0-9]*',q.stdout)) if target.startswith('spawn-denial') else q.returncode==0
 results.append(dict(target=target,command=command,exit=q.returncode,wall_seconds=time.monotonic()-start,stdout=q.stdout,stderr=q.stderr,expected=bool(expected)))
 (p/(tag+'-native-results.json')).write_text(json.dumps(results,indent=2)+'\n');print(target,q.returncode,'expected',bool(expected),flush=True)
 if not expected:sys.exit(1)
print('binary_sha256',hashlib.sha256(out.read_bytes()).hexdigest(),flush=True)
