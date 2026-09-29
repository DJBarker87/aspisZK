#!/usr/bin/env python3
"""Pinned release generator; generation/check before any Lean aggregation."""
import argparse,hashlib,json,os,shutil,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--stage',type=Path,required=True);a=p.parse_args();src=a.control;root=a.stage;assert not root.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==194
for n,h in m['files'].items():assert sha(src/n)==h,n
root.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,root/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json',*m['files']]:
    if not(root/n).exists():(root/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,root/n)
ex=root/'docs/research/v8-no-work-100-20260907/experiments';f=ex/'r40_entry_generator.rs';shutil.copy2(Path(__file__).with_name(f.name),f);c=ex/'performance-host/Cargo.toml';c.write_text(c.read_text()+'\n[[bin]]\nname="r40-entry-generator"\npath="../r40_entry_generator.rs"\n')
for f in[f,c]:m['files'][str(f.relative_to(root))]=sha(f)
m['r40_generator']={'parent_revision':'84059b5296757f31bfc40f0be52e31de76aa2894','control_manifest_sha256':sha(src/'r18-stage.json'),'verifier_changed':False};(root/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
h=json.loads((root/'r17-stage.json').read_text());out=root/'check-a';out.mkdir();target=Path('/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',NO_DNA='1',RUSTFLAGS=h['rustflags'],CARGO_TARGET_DIR=str(target),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
def run(cmd,label):
    print(json.dumps({'phase':label,'command':cmd}),flush=True)
    with(out/(label+'.log')).open('w')as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
    if r.returncode:raise SystemExit(r.returncode)
run(['/home/dombarker/.cargo/bin/cargo','build','--offline','--locked','--release','--jobs','2','--features',h['features'],'--manifest-path',str(c),'--bin','r40-entry-generator'],'compile')
binary=out/'r40-entry-generator';shutil.copy2(target/'release/r40-entry-generator',binary)
prior=Path('/home/dombarker/project-offloads/aspis-r37-source-20260929-b/check-a/results/algebraic-witness-minor.bin')
for mode in['write','check']:run([str(binary),'--'+mode,str(out/'generated'),str(prior)],mode)
(out/'metadata.json').write_text(json.dumps({'source_manifest_sha256':sha(root/'r18-stage.json'),'binary_sha256':sha(binary),'overflow_checks':True,'generated':{f.name:sha(f)for f in sorted((out/'generated').glob('*.lean'))},'full_privacy':False},indent=2)+'\n')
