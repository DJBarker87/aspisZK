from pathlib import Path
import subprocess,hashlib,json,time,sys,resource
p=Path(sys.argv[1]);tag='N90125';src=p/'tools/pv-v263-20261102/native-growth.rs';results=[]
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
exe=p/(tag+'-growth')
cmd=['/home/dombarker/.cargo/bin/rustc','+1.94.1','--edition=2021','--cfg','feature="r1p-check"',
 '--cfg','feature="ct-host-prover"','-C','opt-level=3','-C','debug-assertions=no',
 '-C','overflow-checks=no','-C','panic=abort',str(src),'-o',str(exe)]
start=time.monotonic();q=subprocess.run(cmd,text=True,capture_output=True,timeout=60)
results.append(dict(target='compile scoped-handle Vec growth finite gate',command=cmd,exit=q.returncode,
 wall_seconds=time.monotonic()-start,stdout=q.stdout,stderr=q.stderr,expected=q.returncode==0,
 source_sha256=hashlib.sha256(src.read_bytes()).hexdigest()))
(p/(tag+'-native-results.json')).write_text(json.dumps(results,indent=2)+'\n')
if q.returncode:sys.exit(q.returncode)
cmd=[str(exe)];start=time.monotonic();q=subprocess.run(cmd,text=True,capture_output=True,timeout=60)
rows=[json.loads(line) for line in q.stdout.splitlines()]
(p/(tag+'-growth-observations.json')).write_text(json.dumps(rows,indent=2)+'\n')
results.append(dict(target='fifteen actual scoped-handle pushes for three representative payloads',command=cmd,
 exit=q.returncode,wall_seconds=time.monotonic()-start,stdout=q.stdout,stderr=q.stderr,
 expected=q.returncode==0 and len(rows)==3 and all(r['growth_requests']==[4,8,16] and 1<r['handle_size']<=1024 for r in rows),
 credit='finite native validation of std Vec growth, not actual callback success or whole worker binding'))
(p/(tag+'-native-results.json')).write_text(json.dumps(results,indent=2)+'\n')
cmd=[str(exe),'--bad-growth'];start=time.monotonic();q=subprocess.run(cmd,text=True,capture_output=True,timeout=60)
results.append(dict(target='matched changed-minimum growth control must fail',command=cmd,exit=q.returncode,wall_seconds=time.monotonic()-start,stdout=q.stdout,stderr=q.stderr,expected=q.returncode!=0))
(p/(tag+'-native-results.json')).write_text(json.dumps(results,indent=2)+'\n')
print('three representative handle payloads:',[(r['handle_size'],r['growth_requests']) for r in rows],flush=True)
sys.exit(0 if all(r['expected'] for r in results) else 1)
