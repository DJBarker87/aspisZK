#!/usr/bin/env python3
"""Source-root/chord substitution and one explicit algebraic witness."""
import argparse,hashlib,json,os,shutil,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--stage',type=Path,required=True);a=p.parse_args();src=a.control;root=a.stage;assert not root.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==190
for n,h in m['files'].items():assert sha(src/n)==h,n
root.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,root/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json',*m['files']]:
    if not(root/n).exists():(root/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,root/n)
ex=root/'docs/research/v8-no-work-100-20260907/experiments';f=ex/'r37_restricted_residual.rs';shutil.copy2(Path(__file__).with_name(f.name),f)
fragment=ex/'r37_residual_arithmetic.rs';base=(ex/'r36_residual_model.rs').read_text();assert base.count('fn main(){')==1;fragment.write_text(base.split('fn main(){')[0].replace('//!','//'))
c=ex/'performance-host/Cargo.toml';c.write_text(c.read_text()+'\n[[bin]]\nname="r37-restricted-residual"\npath="../r37_restricted_residual.rs"\n')
for f in[f,fragment,c]:m['files'][str(f.relative_to(root))]=sha(f)
for w in range(2):
    f=src/f'world{w}-prefix.bin';assert sha(f)==m['r28_h1_capacity']['prefixes'][w]['prefix_sha256'];shutil.copy2(f,root/f.name);shutil.copy2(src/f'check-a/world{w}/model-minor.bin',root/f'world{w}-minor.bin')
m['r37_restricted']={'parent_revision':'73cd6b03a759c06714121a90108865fc71c50cce','control_manifest_sha256':sha(src/'r18-stage.json'),'verifier_changed':False};(root/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
h=json.loads((root/'r17-stage.json').read_text());out=root/'check-a';out.mkdir();target=Path('/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',NO_DNA='1',RUSTFLAGS=h['rustflags'],CARGO_TARGET_DIR=str(target),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
def run(cmd,label):
    print(json.dumps({'phase':label,'command':cmd}),flush=True)
    with(out/(label+'.log')).open('w')as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
    if r.returncode:raise SystemExit(r.returncode)
run(['/home/dombarker/.cargo/bin/cargo','build','--offline','--locked','--release','--jobs','2','--features',h['features'],'--manifest-path',str(c),'--bin','r37-restricted-residual'],'compile')
binary=out/'r37-restricted-residual';shutil.copy2(target/'release/r37-restricted-residual',binary);run([str(binary),str(root),str(out/'results')],'checks')
(out/'metadata.json').write_text(json.dumps({'source_manifest_sha256':sha(root/'r18-stage.json'),'binary_sha256':sha(binary),'overflow_checks':True,'full_privacy':False},indent=2)+'\n')
