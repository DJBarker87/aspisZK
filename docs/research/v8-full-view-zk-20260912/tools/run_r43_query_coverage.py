#!/usr/bin/env python3
"""Run targeted symmetry scrutiny with the pinned, cached release implementation."""
import argparse,hashlib,json,os,shutil,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--stage',type=Path,required=True);p.add_argument('--mode',choices=['random','boolean','line','line2','witness'],default='random');a=p.parse_args();src=a.control;root=a.stage;assert not root.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==197
for n,h in m['files'].items():assert sha(src/n)==h,n
root.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,root/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json',*m['files']]:
    if not(root/n).exists():(root/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,root/n)
name='r43-universal-witness'if a.mode=='witness'else'r43-query-coverage';ex=root/'docs/research/v8-no-work-100-20260907/experiments';f=ex/(name.replace('-','_')+'.rs');shutil.copy2(Path(__file__).with_name(f.name),f);c=ex/'performance-host/Cargo.toml';c.write_text(c.read_text()+f'\n[[bin]]\nname="{name}"\npath="../{f.name}"\n')
for f in [f,c]:m['files'][str(f.relative_to(root))]=sha(f)
m['r43_query_coverage']={'parent_revision':'0ffa62b927c35a499f15e3412cffb643803ab7ca','control_manifest_sha256':sha(src/'r18-stage.json'),'verifier_changed':False};(root/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
h=json.loads((root/'r17-stage.json').read_text());out=root/'check-a';out.mkdir();target=Path('/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',NO_DNA='1',RUSTFLAGS=h['rustflags'],CARGO_TARGET_DIR=str(target),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true');commands=[]
def run(cmd,label):
    print(json.dumps({'phase':label,'command':cmd}),flush=True)
    with(out/(label+'.log')).open('w')as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
    commands.append({'phase':label,'command':cmd,'exit':r.returncode});print((out/(label+'.log')).read_text(),flush=True)
    if r.returncode:raise SystemExit(r.returncode)
run(['/home/dombarker/.cargo/bin/cargo','build','--offline','--locked','--release','--jobs','2','--features',h['features'],'--manifest-path',str(c),'--bin',name],'compile')
binary=out/name;shutil.copy2(target/'release'/name,binary);run([str(binary),str(out/'results')if a.mode=='witness'else a.mode],'coverage')
(out/'metadata.json').write_text(json.dumps({'source_manifest_sha256':sha(root/'r18-stage.json'),'binary_sha256':sha(binary),'overflow_checks':True,'commands':commands,'accepted_prefix':False,'universal_rank':False,'full_privacy':False},indent=2)+'\n')
