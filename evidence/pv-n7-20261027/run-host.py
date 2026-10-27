"""Task-local receipt runner. Invoke only in a capped host scope."""
from pathlib import Path
import hashlib,json,os,runpy,subprocess,sys,time
H=Path('/home/dombarker/project-offloads/codex-pv-n7-20261027')
name=sys.argv[1];cmd=sys.argv[2:];O=H/'evidence'/name;O.mkdir(exist_ok=False)
cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert list(limits.values())==['6442450944','8589934592','0','64'],limits
admit=runpy.run_path(str(H/'reservation.py'))['admission'](requested=0)
(O/'admission.json').write_text(json.dumps(admit,indent=2)+'\n')
if not admit['allowed']:sys.exit(78)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTFLAGS='-C link-arg=-Wl,--threads=4',CARGO_TARGET_DIR=str(H/'target'))
rec=dict(target=cmd,source_revision='0c9dc9a4ccd87cc9a4a6590842894a85e56581b2',patch_sha256=hashlib.sha256((H/'0001-private-key-raw-fd.patch').read_bytes()).hexdigest(),limits=limits,print_axioms='N/A: native build/fixture/inspection, no Lean',rustc=subprocess.check_output(['/home/dombarker/.cargo/bin/rustc','-Vv'],text=True),environment={k:env[k] for k in ['RUSTFLAGS','CARGO_TARGET_DIR','PATH']})
(O/'preflight.json').write_text(json.dumps(rec,indent=2)+'\n');t=time.monotonic()
with (O/'stdout.log').open('w') as so,(O/'stderr.log').open('w') as se:
 r=subprocess.run(['/usr/bin/time','-v','-o',str(O/'time.log'),*cmd],env=env,stdout=so,stderr=se)
rec.update(exit_status=r.returncode,wall_seconds=time.monotonic()-t,cgroup_memory_peak_bytes=int((cg/'memory.peak').read_text()),cgroup_swap_peak_bytes=int((cg/'memory.swap.peak').read_text()))
(O/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec));sys.exit(r.returncode)
