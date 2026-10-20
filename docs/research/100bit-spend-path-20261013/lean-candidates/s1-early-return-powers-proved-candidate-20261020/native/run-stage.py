from pathlib import Path
import subprocess,time,json,hashlib,re
W=Path(__file__).resolve().parent;E=W/'evidence';E.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
compiler=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/bin/rustc')
CG=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().removeprefix('0::').lstrip('/')
limits={x:(CG/x).read_text().strip() for x in ['memory.high','memory.max','memory.swap.max']};assert limits=={'memory.high':str(512*1024**2),'memory.max':str(1024**3),'memory.swap.max':'0'}
pre={'compiler':str(compiler),'compiler_sha256':sha(compiler),'version':subprocess.check_output([str(compiler),'--version'],text=True).strip(),'limits':limits,'source_hashes':{str(p.relative_to(W)):sha(p) for p in (W/'input').rglob('*.rs')},'scope':'CANDIDATE native randomized equivalence only; not SBF/CU or cryptographic theorem'};(E/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
commands=[('compile',[str(compiler),'--edition','2021','-C','opt-level=3','-C','overflow-checks=on','--cfg','feature="r0"','--cfg','feature="private-leaf-salts"',str(W/'input/main.rs'),'-o',str(W/'native-check')]),('test',[str(W/'native-check')])]
for name,cmd in commands:
 (E/(name+'-command.json')).write_text(json.dumps(cmd,indent=2)+'\n');before=(CG/'memory.events').read_text();start=time.monotonic()
 with (E/(name+'.log')).open('w') as log:
  result=subprocess.run(['/usr/bin/time','-v','-o',str(E/(name+'-time.log')),*cmd],cwd=W,stdout=log,stderr=subprocess.STDOUT,timeout=60)
 timing=(E/(name+'-time.log')).read_text();m=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',timing)
 rec={'exit_status':result.returncode,'wall_seconds':round(time.monotonic()-start,3),'peak_process_rss_kib':int(m[1]) if m else None,'scope_memory_peak_bytes':int((CG/'memory.peak').read_text()),'scope_swap_peak_bytes':int((CG/'memory.swap.current').read_text()),'memory_events_before':before,'memory_events_after':(CG/'memory.events').read_text()}
 if name=='test' and result.returncode==0:rec['sample_inputs_sha256']=sha(W/'sample-inputs.json');rec['binary_sha256']=sha(W/'native-check')
 (E/(name+'-receipt.json')).write_text(json.dumps(rec,indent=2)+'\n');print(name,json.dumps(rec),flush=True)
 if result.returncode:print((E/(name+'.log')).read_text()[:4000]);raise SystemExit(result.returncode)
print((E/'test.log').read_text(),flush=True)
