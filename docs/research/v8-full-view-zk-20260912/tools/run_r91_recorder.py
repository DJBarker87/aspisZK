#!/usr/bin/env python3
"""Focused trace-recorder release tests after removing the large array copy."""
import argparse,hashlib,json,os,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);a=p.parse_args();s=a.stage
m=json.loads((s/'r18-stage.json').read_text());assert m['r91_wide']['heap_recorder']
for n,h in m['files'].items():assert hashlib.sha256((s/n).read_bytes()).hexdigest()==h,n
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
caps={n:(cg/n).read_text().strip()for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert list(caps.values())==[str(5*2**30),str(7*2**30),'0','128']
out=s/'r91-recorder';assert not out.exists();out.mkdir()
(out/'resources.json').write_text(json.dumps(caps,indent=2)+'\n')
env=dict(os.environ,NO_DNA='1',PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',
 CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',
 CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
env.pop('RUSTFLAGS',None)
cmd=['/home/dombarker/.cargo/bin/cargo','test','--offline','--locked','--release','--jobs','2',
 '--manifest-path',str(s/'Cargo.toml'),'-p','aspis-statement','--lib','trace_v4::tests::','--','--nocapture']
(out/'command.json').write_text(json.dumps(cmd,indent=2)+'\n')
with (out/'test.log').open('w')as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],env=env,cwd=s,stdout=f,stderr=subprocess.STDOUT)
(out/'receipt.json').write_text(json.dumps({'exit':r.returncode,'manifest_sha256':hashlib.sha256((s/'r18-stage.json').read_bytes()).hexdigest()},indent=2)+'\n')
print((out/'test.log').read_text()[-6000:]);raise SystemExit(r.returncode)
