#!/usr/bin/env python3
"""Run inside bounded Linux scope; cached optimized tests, no full replay."""
import argparse,hashlib,json,os,subprocess
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True)
p.add_argument('--test',default='r19_opening')
p.add_argument('--bin',default='aspis-v8-performance-host')
p.add_argument('--run',action='store_true')
p.add_argument('--cfg',default='')
a=p.parse_args();root=a.stage.resolve()
meta=json.loads((root/'r18-stage.json').read_text())
for name,h in meta['files'].items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==h,name
host=json.loads((root/'r17-stage.json').read_text())
env=dict(os.environ,NO_DNA='1',PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',
 RUSTFLAGS=host['rustflags']+(' --cfg '+a.cfg if a.cfg else ''),CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
cmd=['/home/dombarker/.cargo/bin/cargo','run' if a.run else 'test','--release','--offline','--locked','--jobs','2',
 '--manifest-path',str(root/'docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml'),
 '--features',host['features'],'--bin',a.bin]
if not a.run:cmd += [a.test,'--','--nocapture','--test-threads=1']
print(json.dumps({'stage':str(root),'phase':'compile then focused optimized source gate','command':cmd,'rustflags':host['rustflags']}),flush=True)
raise SystemExit(subprocess.run(['/usr/bin/time','-v']+cmd,cwd=root,env=env).returncode)
