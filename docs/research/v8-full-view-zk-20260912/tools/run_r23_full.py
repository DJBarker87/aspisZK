#!/usr/bin/env python3
"""Bounded build-host only. Release full-source checks and unchanged-proof SVM."""
import argparse,hashlib,json,os,shutil,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);p.add_argument('--mode',choices=['host','sbf','svm'],required=True);a=p.parse_args();s=a.stage;here=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((s/'r18-stage.json').read_text());composed='r24_compose' in m
assert len(m['files'])==((176 if 'r24_qm' in m else 175) if composed else 174) and m['r23_width']['rewrite_sites']==2
for n,h in m['files'].items():assert sha(s/n)==h,n
env=dict(os.environ,NO_DNA='1',PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
out=s/(('r24-' if composed else 'r23-')+a.mode+'-a');assert not out.exists();out.mkdir()
def run(name,cmd):
    with (out/name).open('w')as f:subprocess.run(['/usr/bin/time','-v']+cmd,env=env,cwd=s,stdout=f,stderr=subprocess.STDOUT,check=True)
fixtures=[Path('/home/dombarker/project-offloads/aspis-r19-channel-20260921-c/host-c')/n for n in ['fixture-world0','fixture-world1-resumed']]
ex=s/'docs/research/v8-no-work-100-20260907/experiments'
if a.mode=='host':
    meta=json.loads((s/'r17-stage.json').read_text());cache=Path('/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
    env.update(RUSTFLAGS=meta['rustflags'],CARGO_TARGET_DIR=str(cache))
    run('compile.log',['/home/dombarker/.cargo/bin/cargo','build','--release','--offline','--locked','--jobs','2','--manifest-path',str(ex/'performance-host/Cargo.toml'),'--features',meta['features'],'--bin','aspis-v8-performance-host'])
    shutil.copy2(cache/'release/aspis-v8-performance-host',out/'r19-host')
    run('wire-controls.log',['python3',str(here/'check_r19_wire_controls.py'),'--binary',str(out/'r19-host'),'--fixture',str(fixtures[0]),'--output',str(out/'wire-controls')])
    for i,f in enumerate(fixtures):run(f'world{i}.log',[str(out/'r19-host'),'--audit-existing',str(f)])
elif a.mode=='sbf':
    run('compile.log',['python3',str(here/'build_r20_sbf.py'),'--stage',str(s),'--mode','primary'])
else:
    binary=Path('/home/dombarker/project-offloads/aspis-r20-svm-20260922-a/r20-svm-probe');elf=s/'sbf-primary/aspis_v8_performance_sbf.so';results=[]
    build=s/(('r24-' if composed else 'r23-')+'sbf-a')
    build_env=json.loads((build/'environment.json').read_text())
    assert build_env['source_manifest_sha256']==sha(s/'r18-stage.json')
    build_log=(build/'compile.log').read_text()
    assert 'overflows the maximum allowed frame' not in build_log
    assert not ('Stack offset' in build_log and 'exceeded' in build_log)
    if 'elf_sha256' in build_env:assert build_env['elf_sha256']==sha(elf)
    for i,f in enumerate(fixtures):
        run(f'world{i}.log',[str(binary),str(elf),str(f)])
        rows=[json.loads(l) for l in (out/f'world{i}.log').read_text().splitlines() if l.startswith('{')]
        assert len(rows)==4
        high=next(r for r in rows if r['case']=='honest' and r['cu_limit']==100000000);assert high['accepted']
        bad=next(r for r in rows if r['case']=='bad-combined-final' and r['cu_limit']==100000000);assert bad['custom_rejection'] and not bad['resource_failure']
        assert all(r['heap_bytes']==262144 and r['unchanged_accounts'] for r in rows)
        results.append({'world':i,'fixture':str(f),'proof_sha256':sha(f/'proof-1.bin'),'results':rows})
    (out/'receipt.json').write_text(json.dumps({'source_manifest_sha256':sha(s/'r18-stage.json'),'elf_sha256':sha(elf),'driver_sha256':sha(binary),'full_verifier':True,'scalar_transpose_installed':composed,'instrumented':bool(m.get('r24_profile')),'runs':results},indent=2)+'\n')
    print(json.dumps([{'world':r['world'],'honest':[(x['cu_limit'],x['cu'],x['accepted']) for x in r['results'] if x['case']=='honest']}for r in results]))
environment={'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':env['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS'],'source_manifest_sha256':sha(s/'r18-stage.json')}
if a.mode=='sbf':environment['elf_sha256']=sha(s/'sbf-primary/aspis_v8_performance_sbf.so')
(out/'environment.json').write_text(json.dumps(environment,indent=2)+'\n')
