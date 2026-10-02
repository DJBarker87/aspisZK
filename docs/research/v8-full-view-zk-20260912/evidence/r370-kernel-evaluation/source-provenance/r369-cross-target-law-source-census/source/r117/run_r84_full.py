#!/usr/bin/env python3
"""Full compact candidate experiment; NEW proofs/profile, never security promotion."""
import argparse,hashlib,json,os,shutil,subprocess,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);p.add_argument('--mode',choices=['host','sbf','svm'],required=True);a=p.parse_args()
s=a.stage.resolve();here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
m=json.loads((s/'r18-stage.json').read_text());assert 'r84_compact' in m
for n,h in m['files'].items():assert sha(s/n)==h,n
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
caps={n:(cg/n).read_text().strip()for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
hi,ma={'host':(5,7),'sbf':(12,16),'svm':(2,3)}[a.mode]
assert caps=={'memory.high':str(hi*2**30),'memory.max':str(ma*2**30),'memory.swap.max':'0','pids.max':'128'}
out=s/f'r24-{a.mode}-a';assert not out.exists();out.mkdir();(out/'resources.json').write_text(json.dumps(caps,indent=2)+'\n')
env=dict(os.environ,NO_DNA='1',PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
for n in list(env):
    if n.startswith('ASPIS_'):env.pop(n)
ex=s/'docs/research/v8-no-work-100-20260907/experiments'
cache=Path('/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
meta=json.loads((s/'r17-stage.json').read_text());records=[]
def run(name,cmd):
    print(json.dumps({'phase':name,'command':cmd}),flush=True);start=time.monotonic()
    with (out/name).open('w')as f:r=subprocess.run(['/usr/bin/time','-v']+cmd,env=env,cwd=s,stdout=f,stderr=subprocess.STDOUT)
    records.append({'name':name,'exit':r.returncode,'wall_s':time.monotonic()-start})
    (out/'commands.json').write_text(json.dumps(records,indent=2)+'\n');assert r.returncode==0,(name,r.returncode)
def compile(binary):
    run(binary+'-compile.log',['/home/dombarker/.cargo/bin/cargo','build','--offline','--locked','--release','--jobs','2','--features',meta['features'],'--manifest-path',str(ex/'performance-host/Cargo.toml'),'--bin',binary])
fixtures=[s/'r24-host-a'/f'fixture-world{w}'for w in range(2)]
if a.mode=='host':
    env.update(RUSTFLAGS=meta['rustflags'],CARGO_TARGET_DIR=str(cache))
    compile('r84-bitperm-check');run('compact-check.log',[str(cache/'release/r84-bitperm-check')])
    compile('r55-opening-check');run('opening-check.log',[str(cache/'release/r55-opening-check')])
    compile('aspis-v8-performance-host');binary=out/'r84-host';shutil.copy2(cache/'release/aspis-v8-performance-host',binary)
    for w,f in enumerate(fixtures):
        env.update(ASPIS_R16_SELECTED_SECOND=str(w),ASPIS_V8_POSITIVE_CASE='honest')
        run(f'generate-world{w}.log',[str(binary),str(f)])
        run(f'world{w}.log',[str(binary),'--audit-existing',str(f)])
    run('wire-controls.log',['python3',str(here/'check_r19_wire_controls.py'),'--binary',str(binary),'--fixture',str(fixtures[0]),
        '--old-fixture','/home/dombarker/project-offloads/aspis-r19-channel-20260921-c/host-c/fixture-world0','--output',str(out/'wire-controls')])
elif a.mode=='sbf':
    assert 'compact_source_implemented=true' in (s/'r24-host-a/compact-check.log').read_text()
    for w in range(2):assert 'R17_PUBLIC_PREFIX_ACCEPTED' in (s/f'r24-host-a/world{w}.log').read_text()
    run('compile.log',['python3',str(here/'build_r84_sbf.py'),'--stage',str(s),'--mode','primary'])
    unstripped=cache.parent.parent/'performance-sbf/target/sbpf-solana-solana/release/aspis_v8_performance_sbf.so'
    shutil.copy2(unstripped,s/'aspis-unstripped.so')
else:
    binary=Path('/home/dombarker/project-offloads/aspis-r20-svm-20260922-a/r20-svm-probe');elf=s/'sbf-primary/aspis_v8_performance_sbf.so'
    build=(s/'r24-sbf-a/compile.log').read_text();assert 'overflows the maximum allowed frame' not in build and not('Stack offset' in build and 'exceeded' in build)
    results=[]
    for w,f in enumerate(fixtures):
        run(f'world{w}.log',[str(binary),str(elf),str(f)])
        rows=[json.loads(l)for l in (out/f'world{w}.log').read_text().splitlines()if l.startswith('{')]
        assert len(rows)==4
        high=next(r for r in rows if r['case']=='honest'and r['cu_limit']==100000000);assert high['accepted']
        bad=next(r for r in rows if r['case']=='bad-combined-final'and r['cu_limit']==100000000);assert bad['custom_rejection']and not bad['resource_failure']
        assert all(r['heap_bytes']==262144 and r['unchanged_accounts']for r in rows)
        results.append({'world':w,'proof_sha256':sha(f/'proof-1.bin'),'results':rows})
    (out/'receipt.json').write_text(json.dumps({'source_manifest_sha256':sha(s/'r18-stage.json'),'elf_sha256':sha(elf),'driver_sha256':sha(binary),'new_profile':True,'full_verifier':True,'security_promoted':False,'runs':results},indent=2)+'\n')
    print(json.dumps(results),flush=True)
environment={'source_manifest_sha256':sha(s/'r18-stage.json'),'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true'}
if a.mode=='sbf':environment['elf_sha256']=sha(s/'sbf-primary/aspis_v8_performance_sbf.so')
(out/'environment.json').write_text(json.dumps(environment,indent=2)+'\n')
