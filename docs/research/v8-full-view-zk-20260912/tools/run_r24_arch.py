#!/usr/bin/env python3
"""Isolated target-ISA experiment on a frozen complete-verifier stage."""
import argparse,hashlib,json,os,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--arch',choices=['v3'],default='v3');p.add_argument('--mode',choices=['build','svm'],required=True);a=p.parse_args();s=a.stage;out=a.output
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((s/'r18-stage.json').read_text());assert 'r24_compose' in m and 'r24_profile' not in m
for n,h in m['files'].items():assert sha(s/n)==h,n
env=dict(os.environ,NO_DNA='1',PATH='/home/dombarker/.cargo/bin:/home/dombarker/.local/share/solana/install/active_release/bin:/usr/bin:/bin',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
def run(log,cmd):
    with log.open('w')as f:subprocess.run(['/usr/bin/time','-v']+cmd,env=env,cwd=s,stdout=f,stderr=subprocess.STDOUT,check=True)
if a.mode=='build':
    assert not out.exists();out.mkdir()
    probe=json.loads((s/'r17-sbf-probe.json').read_text())
    env.update(RUSTFLAGS=probe['rustflags']+' --cfg r18_primary_only',RUSTC='/home/dombarker/.cache/solana/v1.54/platform-tools/rust/bin/rustc',CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-sbf/target')
    cmd=['/home/dombarker/.local/share/solana/install/active_release/bin/cargo-build-sbf','--arch',a.arch,'--offline','--skip-tools-install','--no-rustup-override','--tools-version','v1.54','--jobs','2','--features',probe['features'],'--manifest-path',str(s/probe['manifest']),'--sbf-out-dir',str(out/'sbf')]
    run(out/'compile.log',cmd)
    log=(out/'compile.log').read_text();assert 'overflows the maximum allowed frame' not in log and not('Stack offset' in log and 'exceeded' in log)
    elf=out/'sbf/aspis_v8_performance_sbf.so'
    (out/'build.json').write_text(json.dumps({'command':cmd,'arch':a.arch,'source_manifest_sha256':sha(s/'r18-stage.json'),'elf_sha256':sha(elf),'exit':0,'overflow_checks':True,'network_deployability_claim':False},indent=2)+'\n')
else:
    meta=json.loads((out/'build.json').read_text());elf=out/'sbf/aspis_v8_performance_sbf.so'
    assert meta['source_manifest_sha256']==sha(s/'r18-stage.json') and meta['elf_sha256']==sha(elf)
    dst=out/'svm';assert not dst.exists();dst.mkdir()
    driver=Path('/home/dombarker/project-offloads/aspis-r20-svm-20260922-a/r20-svm-probe');runs=[]
    for w,name in enumerate(['fixture-world0','fixture-world1-resumed']):
        f=Path('/home/dombarker/project-offloads/aspis-r19-channel-20260921-c/host-c')/name
        log=dst/f'world{w}.log';run(log,[str(driver),str(elf),str(f)])
        rows=[json.loads(l)for l in log.read_text().splitlines()if l.startswith('{')];assert len(rows)==4
        assert all(x['heap_bytes']==262144 and x['unchanged_accounts']for x in rows)
        for x in rows:
            if x['cu_limit']==100000000:assert x['accepted'] if x['case']=='honest' else x['custom_rejection'] and not x['resource_failure']
        runs.append({'world':w,'proof_sha256':sha(f/'proof-1.bin'),'results':rows})
    receipt={**meta,'driver_sha256':sha(driver),'full_verifier':True,'runs':runs}
    (dst/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps([{'world':r['world'],'honest':[(x['cu_limit'],x['cu'],x['accepted'])for x in r['results']if x['case']=='honest']}for r in runs]))
