#!/usr/bin/env python3
"""Run only in a bounded NUC scope. Cached release build / named native gate."""
import argparse,hashlib,json,os,shutil,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);p.add_argument('--mode',choices=['host','sbf'],required=True)
a=p.parse_args();stage=a.stage.resolve();assert stage.name.startswith('aspis-r22-')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((stage/'r18-stage.json').read_text());assert 'r22_native' in m
for n,h in m['files'].items():assert sha(stage/n)==h,n
ex=stage/'docs/research/v8-no-work-100-20260907/experiments'
cache=Path('/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments')
env=dict(os.environ,NO_DNA='1',PATH='/home/dombarker/.cargo/bin:/home/dombarker/.local/share/solana/install/active_release/bin:/usr/bin:/bin')
out=stage/a.mode;assert not out.exists();out.mkdir()
if a.mode=='host':
    meta=json.loads((stage/'r17-stage.json').read_text());env.update(CARGO_TARGET_DIR=str(cache/'performance-host/target'),RUSTFLAGS=meta['rustflags'])
    cmd=['/home/dombarker/.cargo/bin/cargo','build','--release','--offline','--locked','--jobs','2','--manifest-path',str(ex/'performance-host/Cargo.toml'),'--features',meta['features'],'--bin','r22-check']
else:
    meta=json.loads((stage/'r17-sbf-probe.json').read_text())
    env.update(CARGO_TARGET_DIR=str(cache/'performance-sbf/target'),RUSTFLAGS=meta['rustflags']+' --cfg r18_primary_only',RUSTC='/home/dombarker/.cache/solana/v1.54/platform-tools/rust/bin/rustc')
    cmd=['/home/dombarker/.local/share/solana/install/active_release/bin/cargo-build-sbf','--offline','--skip-tools-install','--no-rustup-override','--tools-version','v1.54','--jobs','2','--features',meta['features'],'--manifest-path',str(ex/'performance-sbf/Cargo.toml'),'--sbf-out-dir',str(out)]
print(json.dumps({'phase':'compile then native-source gate' if a.mode=='host' else 'cached SBF compilation','command':cmd,'flags':env['RUSTFLAGS']}),flush=True)
with (out/'compile.log').open('w')as f:subprocess.run(['/usr/bin/time','-v']+cmd,env=env,cwd=stage,stdout=f,stderr=subprocess.STDOUT,check=True)
log=(out/'compile.log').read_text();assert 'overflows the maximum allowed frame' not in log and not('Stack offset' in log and 'exceeded' in log)
if a.mode=='host':
    binary=out/'r22-check';shutil.copy2(cache/'performance-host/target/release/r22-check',binary)
    inputs=[Path('/home/dombarker/project-offloads/aspis-r21-tools-20260922-a')/f'public-world{w}.bin' for w in range(2)]
    with (out/'check.log').open('w')as f:subprocess.run(['/usr/bin/time','-v',str(binary),str(out/'generated'),*map(str,inputs)],env=env,cwd=stage,stdout=f,stderr=subprocess.STDOUT,check=True)
    for w in range(2):
        old=Path(f'/home/dombarker/project-offloads/aspis-r21-helper-20260922-c/host-world{w}/generated/helper.bin').read_bytes()
        assert (out/f'generated/world{w}.bin').read_bytes()==old[:400]
(out/'metadata.json').write_text(json.dumps({'source_manifest_sha256':sha(stage/'r18-stage.json'),'command':cmd,'flags':env['RUSTFLAGS'],'artifact_sha256':sha(out/('r22-check' if a.mode=='host' else 'aspis_v8_performance_sbf.so')),'scope':'native ordinary+image only'},indent=2)+'\n')
