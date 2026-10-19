#!/usr/bin/env python3
"""One focused optimized Rust test in an existing mandatory capped scope."""
import hashlib,json,os,subprocess,sys,time,signal
from pathlib import Path
root=Path('/home/dombarker/project-offloads/aspis-r1-r18-prefix-20261016')
label=sys.argv[1]
out=root/'runs'/label
out.mkdir(parents=True,exist_ok=False)
(out/'runner.py').write_bytes(Path(__file__).read_bytes())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=root/'source-manifest.json'
harness_manifest=root/'harness-manifest.json'
harness=json.loads(harness_manifest.read_text())
for p,s in harness['files'].items():
 assert sha(root/'source'/p)==s,p
pins=json.loads(manifest.read_text())
for p,s in pins['files'].items():
 assert sha(root/'source'/p)==s,p
cg=Path('/sys/fs/cgroup')/next(s.split(':',2)[2] for s in Path('/proc/self/cgroup').read_text().splitlines() if s.startswith('0::')).lstrip('/')
read=lambda k:(cg/k).read_text().strip()
limits={k:read(k) for k in ['memory.high','memory.max','memory.swap.max']}
assert limits=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0'},limits
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(root/'cargo-target'),CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true')
for k in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS']:
 env.pop(k,None)
cmd=['/usr/bin/time','-v','-o',str(out/'time.log'),'/home/dombarker/.cargo/bin/cargo','build','--release','--locked','--offline','--manifest-path','tools/r1-cost-probe/Cargo.toml','--features','private-leaf-salts','--bin','r18_replay','--jobs','1']
r={'label':label,'source_revision':harness['source_revision'],'harness_manifest_sha256':sha(harness_manifest),'source_parent_revision':pins['parent_revision'],'source_manifest_sha256':sha(manifest),'wire_source_sha256':pins['files']['crates/aspis-r1-cost-probe/src/r1_wire.rs'],'runner_sha256':sha(Path(__file__)),'command':cmd,'cwd':str(root/'source'),'environment':{k:env[k] for k in ['PATH','CARGO_TARGET_DIR','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE']},'cgroup':str(cg),'limits':limits,'events_before':read('memory.events'),'start_unix':time.time(),'rustc_version':subprocess.check_output(['rustc','-Vv'],env=env,text=True),'cargo_version':subprocess.check_output(['cargo','-V'],env=env,text=True),'expected_work':'optimized native harness compilation only; no harness execution, SBF build or proof generation'}
(out/'preflight.json').write_text(json.dumps(r,indent=2)+'\n')
start=time.monotonic();peak=0
with (out/'test.log').open('w') as log:
 p=subprocess.Popen(cmd,cwd=root/'source',env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 while p.poll() is None:
  peak=max(peak,int(read('memory.current')))
  if time.monotonic()-start>600:
   os.killpg(p.pid,signal.SIGKILL);r['timeout']=True;break
  time.sleep(.2)
 p.wait()
if p.returncode==0:
 r['binary_sha256']=sha(root/'cargo-target/release/r18_replay')
r.update(exit=p.returncode,wall_seconds=time.monotonic()-start,cgroup_peak_bytes=int(read('memory.peak')),sampled_peak_bytes=peak,events_after=read('memory.events'),swap_current_bytes=int(read('memory.swap.current')))
(out/'receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['label','exit','wall_seconds','cgroup_peak_bytes','swap_current_bytes']}),flush=True)
print((out/'test.log').read_text()[-3500:],flush=True)
sys.exit(p.returncode)
