from pathlib import Path
import subprocess,hashlib,json,time,sys,resource,re
p=Path(sys.argv[1]);tag='N90124';src=p/'tools/pv-v263-20261102/native-counter.rs';results=[]
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
pins=json.loads((p/'evidence/pv-v263-20261102/frozen-source.json').read_text())
for pin in pins['files']:
 q=p/'evidence/pv-v263-20261102/inputs'/pin['path']
 assert hashlib.sha256(q.read_bytes()).hexdigest()==pin['sha256'],pin['path']
for label,extra,expected in [('deployed-no-trace',[],'i32'),
 ('trace-counterpart',['--cfg','feature="public-work-trace"'],'usize')]:
 out=p/(tag+'-'+label+'.mir.txt')
 cmd=['/home/dombarker/.cargo/bin/rustc','+1.94.1','--edition=2021','--cfg','feature="r1p-check"',
 '--cfg','feature="ct-host-prover"','-C','opt-level=3','-C','debug-assertions=no',
 '-C','overflow-checks=no','-C','panic=abort','--emit=mir',*extra,str(src),'-o',str(out)]
 start=time.monotonic();q=subprocess.run(cmd,text=True,capture_output=True,timeout=60)
 record=dict(target=label,command=cmd,exit=q.returncode,wall_seconds=time.monotonic()-start,
 stdout=q.stdout,stderr=q.stderr,expected_type=expected,credit='compiler type inference on frozen helper; isolated harness, no actual callback success')
 results.append(record)
 if q.returncode:
  (p/(tag+'-native-results.json')).write_text(json.dumps(results,indent=2)+'\n');sys.exit(1)
 mir=out.read_text();lines=[line for line in mir.splitlines() if 'Vec<T>, '+expected in line]
 record.update(mir_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),mir_bytes=out.stat().st_size,
 counter_type_lines=lines,expected=bool(lines))
 (p/(tag+'-native-results.json')).write_text(json.dumps(results,indent=2)+'\n')
 print(label,'exit',q.returncode,'counter',expected,'type lines',len(lines),flush=True)
 if not lines:sys.exit(1)
