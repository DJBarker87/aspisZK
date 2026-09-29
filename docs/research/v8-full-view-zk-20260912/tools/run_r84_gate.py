#!/usr/bin/env python3
"""Focused source leaf, then optimized real opposite-witness prefix preflight."""
import argparse,hashlib,json,os,shutil,subprocess,time
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True)
p.add_argument('--mode',choices=['leaf','prefix'],required=True)
p.add_argument('--world',type=int,choices=[0,1],default=0)
p.add_argument('--through-g',action='store_true')
a=p.parse_args();stage=a.stage.resolve();m=json.loads((stage/'r18-stage.json').read_text())
assert m['r84_bitperm']['host_only_preflight']
for n,h in m['files'].items():assert hashlib.sha256((stage/n).read_bytes()).hexdigest()==h,n
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
caps={n:(cg/n).read_text().strip()for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert caps=={'memory.high':str(5*2**30),'memory.max':str(7*2**30),'memory.swap.max':'0','pids.max':'128'}
out=stage/('r84-leaf'if a.mode=='leaf'else f'r84-prefix-world{a.world}')
assert not out.exists();out.mkdir();(out/'resources.json').write_text(json.dumps(caps,indent=2)+'\n')
ex=stage/'docs/research/v8-no-work-100-20260907/experiments'
cache=Path('/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
h=json.loads((stage/'r17-stage.json').read_text())
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',NO_DNA='1',RUSTFLAGS=h['rustflags'],CARGO_TARGET_DIR=str(cache),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
for n in list(env):
    if n.startswith('ASPIS_'):env.pop(n)
(out/'environment.json').write_text(json.dumps({k:env[k]for k in ['RUSTFLAGS','CARGO_TARGET_DIR','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS','NO_DNA']},indent=2)+'\n')
records=[]
def run(name,cmd):
    print(json.dumps({'phase':name,'optimized':True,'command':cmd}),flush=True)
    start=time.monotonic()
    with (out/(name+'.log')).open('w')as f:
        r=subprocess.run(['/usr/bin/time','-v']+cmd,cwd=stage,env=env,stdout=f,stderr=subprocess.STDOUT)
    records.append({'phase':name,'command':cmd,'exit':r.returncode,'wall_s':time.monotonic()-start})
    (out/'receipt.json').write_text(json.dumps({'source_manifest_sha256':hashlib.sha256((stage/'r18-stage.json').read_bytes()).hexdigest(),'profile':m['profile'],'commands':records,'complete_proof':False,'security_promoted':False},indent=2)+'\n')
    assert r.returncode==0,(name,r.returncode)
binary='r84-bitperm-check'if a.mode=='leaf'else'aspis-v8-performance-host'
if a.mode=='prefix':
    assert 'R84_FUNCTIONAL' in (stage/'r84-leaf/check.log').read_text()
run('compile',['/home/dombarker/.cargo/bin/cargo','build','--offline','--locked','--release','--jobs','2','--features',h['features'],'--manifest-path',str(ex/'performance-host/Cargo.toml'),'--bin',binary])
saved=out/binary;shutil.copy2(cache/'release'/binary,saved)
if a.mode=='leaf':run('check',[str(saved)])
else:
    env.update(ASPIS_R16_SELECTED_SECOND=str(a.world),ASPIS_V8_POSITIVE_CASE='honest',ASPIS_R17_C1_WITNESS_AUDIT='1',ASPIS_R84_H1_PREFLIGHT='1')
    if a.through_g:env['ASPIS_R84_THROUGH_G']='1'
    print('Expected time: genuine proof-prefix generation, then source C1/H1 affine elimination; release=true, no SBF run.',flush=True)
    run('prefix',[str(saved),str(out/'incomplete-fixture')])
