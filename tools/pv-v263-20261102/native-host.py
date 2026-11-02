from pathlib import Path
import subprocess,hashlib,json,time,sys
p=Path(sys.argv[1]);src=p/'tools/pv-v263-20261102/native.rs';out=p/'native';r=[]
cmd=['/home/dombarker/.cargo/bin/rustc','+1.94.1','--edition=2021','-C','opt-level=3','-C','debug-assertions=no','-C','overflow-checks=no','-C','panic=unwind',str(src),'-o',str(out)]
for label,c in [('compile',cmd),('ordered-results-and-panics',[str(out),'success']),('thread-resource-failure',[str(out),'failure'])]:
 start=time.monotonic();q=subprocess.run(c,text=True,capture_output=True);x=dict(target=label,command=c,exit=q.returncode,wall_seconds=time.monotonic()-start,stdout=q.stdout,stderr=q.stderr);r.append(x);(p/'native-results.json').write_text(json.dumps(r,indent=2)+'\n');print(label,q.returncode,flush=True)
 if q.returncode:sys.exit(q.returncode)
print('binary_sha256',hashlib.sha256(out.read_bytes()).hexdigest())
