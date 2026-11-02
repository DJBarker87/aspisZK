from pathlib import Path
import subprocess,hashlib,json,time,sys,resource
p=Path(sys.argv[1]);tag='N90123';src=p/'tools/pv-v263-20261102/native-drain.rs';out=p/'native-drain';results=[]
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
cmd=['/home/dombarker/.cargo/bin/rustc','+1.94.1','--edition=2021','--cfg','feature="r1p-check"','--cfg','feature="ct-host-prover"','-C','opt-level=3','-C','debug-assertions=no','-C','overflow-checks=no','-C','panic=abort',str(src),'-o',str(out)]
for target,command in [('compile-optimized-drain-harness',cmd),('finite-Vec-drain-and-worker-source-differential',[str(out)])]:
 start=time.monotonic();q=subprocess.run(command,text=True,capture_output=True,timeout=60)
 results.append(dict(target=target,command=command,exit=q.returncode,wall_seconds=time.monotonic()-start,stdout=q.stdout,stderr=q.stderr,expected=q.returncode==0))
 (p/(tag+'-native-results.json')).write_text(json.dumps(results,indent=2)+'\n');print(target,q.returncode,flush=True)
 if q.returncode:sys.exit(1)
print('binary_sha256',hashlib.sha256(out.read_bytes()).hexdigest(),flush=True)
