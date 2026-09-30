#!/usr/bin/env python3
"""Capped host/SBF/SVM AUTHENTICATION-ONLY gate. Never reports Aspis acceptance."""
import argparse,hashlib,json,os,shutil,subprocess,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);p.add_argument('--mode',choices=['host','sbf','svm'],required=True);a=p.parse_args()
s=a.stage.resolve();m=json.loads((s/'r101-stage.json').read_text())
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
for n,h in m['files'].items():assert sha(s/n)==h,n
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
caps={n:(cg/n).read_text().strip()for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
hi,ma={'host':(5,7),'sbf':(12,16),'svm':(2,3)}[a.mode]
assert caps=={'memory.high':str(hi*2**30),'memory.max':str(ma*2**30),'memory.swap.max':'0','pids.max':'128'}
out=s/a.mode;assert not out.exists();out.mkdir();(out/'resources.json').write_text(json.dumps(caps,indent=2)+'\n')
env=dict(os.environ,NO_DNA='1',PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
for n in list(env):
    if n.startswith('ASPIS_')or n in ['RUSTC','SBF_TRACE_DIR']:env.pop(n)
ex=s/'docs/research/v8-no-work-100-20260907/experiments'
cache=Path('/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments')
meta=json.loads((s/'r17-stage.json').read_text());probe=json.loads((s/'r17-sbf-probe.json').read_text());records=[]
def run(name,cmd,cwd=s):
    print(json.dumps({'phase':name,'command':cmd}),flush=True);start=time.monotonic()
    with(out/name).open('w')as f:r=subprocess.run(['/usr/bin/time','-v']+cmd,env=env,cwd=cwd,stdout=f,stderr=subprocess.STDOUT)
    records.append({'name':name,'command':cmd,'exit':r.returncode,'wall_s':time.monotonic()-start})
    (out/'commands.json').write_text(json.dumps(records,indent=2)+'\n');assert r.returncode==0,(name,r.returncode)
if a.mode=='host':
    env.update(RUSTFLAGS=meta['rustflags'],CARGO_TARGET_DIR=str(cache/'performance-host/target'))
    run('compile.log',['/home/dombarker/.cargo/bin/cargo','build','--release','--offline','--locked','--jobs','2','--features',meta['features'],'--manifest-path',str(ex/'performance-host/Cargo.toml'),'--bin','r101-auth-check'])
    run('check.log',[str(cache/'performance-host/target/release/r101-auth-check'),str(s/'fixtures')])
    env.update(RUSTFLAGS='',CARGO_TARGET_DIR=str(cache/'performance-svm/target'))
    run('driver-compile.log',['/home/dombarker/.cargo/bin/cargo','build','--release','--offline','--locked','--jobs','2','--manifest-path',str(s/'svm-driver/Cargo.toml')])
    shutil.copy2(cache/'performance-svm/target/release/aspis-r17-svm-probe',s/'r101-driver')
elif a.mode=='sbf':
    assert 'independent_full_trees=true actual_proofs=false'in(s/'host/check.log').read_text()
    env.update(PATH='/home/dombarker/.cargo/bin:/home/dombarker/.local/share/solana/install/active_release/bin:/usr/bin:/bin',
      RUSTC='/home/dombarker/.cache/solana/v1.54/platform-tools/rust/bin/rustc',RUSTFLAGS=probe['rustflags'],CARGO_TARGET_DIR=str(cache/'performance-sbf/target'))
    run('compile.log',['/home/dombarker/.local/share/solana/install/active_release/bin/cargo-build-sbf','--offline','--skip-tools-install','--no-rustup-override','--tools-version','v1.54','--jobs','2','--features',probe['features'],'--manifest-path',str(ex/'performance-sbf/Cargo.toml'),'--sbf-out-dir',str(out/'elf')])
    log=(out/'compile.log').read_text()
    assert not any(x in log for x in ['overflows the maximum allowed frame','overwrites values in the frame','Stack offset'])
    shutil.copy2(cache/'performance-sbf/target/sbpf-solana-solana/release/aspis_v8_performance_sbf.so',s/'r101-unstripped.so')
else:
    elf=s/'sbf/elf/aspis_v8_performance_sbf.so';results=[]
    for arity in [2,4,8]:
        for world in range(2):
            f=s/'fixtures'/f'a{arity}-world{world}';log=f'a{arity}-world{world}.log'
            run(log,[str(s/'r101-driver'),str(elf),str(f)])
            rows=[json.loads(l)for l in(out/log).read_text().splitlines()if l.startswith('{')];assert len(rows)==4
            assert all(r['heap_bytes']==262144 and r['unchanged_accounts']for r in rows)
            assert all(r['accepted']and not r['resource_failure']for r in rows if r['case']=='honest')
            assert all(r['custom_rejection']and not r['resource_failure']and 'Custom(101)'in r['error']for r in rows if r['case']=='bad-auth-root')
            results.append({'arity':arity,'world':world,'input_sha256':sha(f/'proof-1.bin'),'input_bytes':(f/'proof-1.bin').stat().st_size,'results':rows})
    receipt={'source_manifest_sha256':sha(s/'r101-stage.json'),'elf_sha256':sha(elf),'driver_sha256':sha(s/'r101-driver'),
      'full_verifier':False,'under_1M_full_verifier':False,'synthetic_public_leaves':True,'security_promoted':False,'runs':results}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'auth_only':True,'complete_verifier':False,'results':[
      {'arity':x['arity'],'world':x['world'],'bytes':x['input_bytes'],'cu':x['results'][0]['cu']}for x in results]}))
(out/'environment.json').write_text(json.dumps({'source_manifest_sha256':sha(s/'r101-stage.json'),
 'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','full_verifier':False},indent=2)+'\n')
