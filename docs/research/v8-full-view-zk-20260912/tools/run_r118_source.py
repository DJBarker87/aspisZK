#!/usr/bin/env python3
"""Focused new-profile residual pilot; most time is cached release compilation."""
import argparse,hashlib,json,os,shutil,subprocess,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--stage',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.stage;here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
caps={n:(cg/n).read_text().strip()for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert caps=={'memory.high':str(5*2**30),'memory.max':str(7*2**30),'memory.swap.max':'0','pids.max':'128'}
assert sha(src/'r18-stage.json')=='26755a4250ec6075005e840565040414b694deb97fb1830fc95aff2692d34fb6'
m=json.loads((src/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';changed=[]
for name in ['r118_source_boundary.rs']:
    shutil.copy2(here/name,ex/name);changed.append(ex/name)
original=(ex/'r17_coupled_audit.rs').read_text();anchor='    pub(super) fn qvector('
assert original.count(anchor)==1
helper=original[:original.index(anchor)]+'    pub(super) fn times_x(v:&[K])->Vec<K>{xt(v)}\n}\n'
(ex/'r118_primal_source.rs').write_text(helper);changed.append(ex/'r118_primal_source.rs')
cargo=ex/'performance-host/Cargo.toml';cargo.write_text(cargo.read_text()+'\n[[bin]]\nname="r118-source-boundary"\npath="../r118_source_boundary.rs"\n');changed.append(cargo)
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r118_boundary']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
 'changed':3,'verifier_changed':False,'profile_changed':False,'accepted_prefix':False,'universal_coverage':False,
 'full_security':False,'primal_helper_source_sha256':sha(ex/'r17_coupled_audit.rs'),
 'primal_helper_exact_prefix':True,'expected_heavy_step':'cached release compilation; only three 13-by-28 eliminations'}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
out=dst/'check-a';out.mkdir();(out/'resources.json').write_text(json.dumps(caps,indent=2)+'\n')
meta=json.loads((src/'r17-stage.json').read_text());cache=Path('/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
env=dict(os.environ,NO_DNA='1',PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTFLAGS=meta['rustflags'],CARGO_TARGET_DIR=str(cache),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
records=[]
def run(name,cmd):
    print(json.dumps({'phase':name,'command':cmd}),flush=True);start=time.monotonic()
    with(out/name).open('w')as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],env=env,cwd=dst,stdout=f,stderr=subprocess.STDOUT)
    records.append({'name':name,'command':cmd,'exit':r.returncode,'wall_s':time.monotonic()-start})
    (out/'commands.json').write_text(json.dumps(records,indent=2)+'\n');assert r.returncode==0,(name,r.returncode)
run('compile.log',['/home/dombarker/.cargo/bin/cargo','build','--offline','--locked','--release','--jobs','2','--features',meta['features'],'--manifest-path',str(cargo),'--bin','r118-source-boundary'])
binary=out/'r118-source-boundary';shutil.copy2(cache/'release/r118-source-boundary',binary)
run('check.log',[str(binary),str(out/'results')])
(out/'metadata.json').write_text(json.dumps({'source_manifest_sha256':sha(dst/'r18-stage.json'),'binary_sha256':sha(binary),'base_revision':'3a4a95e8a5f6d5ee1369c37ae6485ea2b32bf757','overflow_checks':True,'full_security':False},indent=2)+'\n')
print((out/'results/summary.json').read_text())
