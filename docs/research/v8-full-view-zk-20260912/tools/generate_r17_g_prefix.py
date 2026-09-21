#!/usr/bin/env python3
"""Optimized fixed-spectrum generation; invoke inside a bounded Linux scope."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
root=Path(sys.argv[1]).resolve()
exp=root/'docs/research/v8-no-work-100-20260907/experiments'
meta=json.loads((root/'r17-stage.json').read_text())
probe=json.loads((root/'r17-sbf-probe.json').read_text())
for name,expected in probe['g_prefix_files'].items():
    assert hashlib.sha256((exp/name).read_bytes()).hexdigest()==expected
env=dict(os.environ)
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',NO_DNA='1',RUSTFLAGS=meta['rustflags'],
    CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
result=subprocess.run(['/usr/bin/time','-v','/home/dombarker/.cargo/bin/cargo','run',
    '--offline','--locked','--release','--jobs','2','--features',meta['features'],
    '--manifest-path',str(exp/'performance-host/Cargo.toml'),'--bin','r17-g-prefix-generate'],
    env=env,cwd=root,stdout=subprocess.PIPE,check=True)
name='r17_g_prefix_tables.rs';assert not (exp/name).exists()
(exp/name).write_bytes(result.stdout)
sha=hashlib.sha256(result.stdout).hexdigest();probe['g_prefix_files'][name]=sha
(root/'r17-sbf-probe.json').write_text(json.dumps(probe,indent=2)+'\n')
control=json.loads((root/'r17-compact-control.json').read_text());control['files'][name]=sha
(root/'r17-compact-control.json').write_text(json.dumps(control,indent=2)+'\n')
print('PASS: optimized fixed prefix spectrum generated; SHA256='+sha,flush=True)
