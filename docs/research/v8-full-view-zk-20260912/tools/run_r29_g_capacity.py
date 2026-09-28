#!/usr/bin/env python3
"""One optimized multi-RHS elimination and source replay per retained prefix."""
import argparse,hashlib,json,os,shutil,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();assert not a.output.exists();a.output.mkdir();root=a.stage.resolve()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((root/'r18-stage.json').read_text());assert len(m['files'])==185
for n,h in m['files'].items():assert sha(root/n)==h,n
h=json.loads((root/'r17-stage.json').read_text());target=Path('/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',NO_DNA='1',RUSTFLAGS=h['rustflags'],CARGO_TARGET_DIR=str(target),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
def run(cmd,label):
    print(json.dumps({'phase':label,'command':cmd}),flush=True)
    with(a.output/(label+'.log')).open('w')as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
    if r.returncode:raise SystemExit(r.returncode)
run(['/home/dombarker/.cargo/bin/cargo','build','--offline','--locked','--release','--jobs','2','--features',h['features'],'--manifest-path',str(root/'docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml'),'--bin','r29-g-capacity'],'compile')
binary=a.output/'r29-g-capacity';shutil.copy2(target/'release/r29-g-capacity',binary)
for w in range(2):run([str(binary),str(root/f'world{w}-prefix.bin'),str(a.output/f'world{w}')],f'world{w}')
(a.output/'metadata.json').write_text(json.dumps({'source_manifest_sha256':sha(root/'r18-stage.json'),'binary_sha256':sha(binary),'rustflags':h['rustflags'],'overflow_checks':True,'full_privacy':False,'source_prefix_substituted':False},indent=2)+'\n')
