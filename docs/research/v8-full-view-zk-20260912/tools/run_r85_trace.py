#!/usr/bin/env python3
"""Capture one complete unchanged-proof execution, reusing cached tracing deps."""
import argparse,hashlib,json,os,shutil,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);p.add_argument('--project',type=Path,required=True);p.add_argument('--mode',choices=['build','trace'],required=True);p.add_argument('--fixture',type=Path);a=p.parse_args();s=a.stage;project=a.project
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
env=dict(os.environ,NO_DNA='1',PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-svm/target')
def run(log,cmd):
    with log.open('w')as f:subprocess.run(['/usr/bin/time','-v']+cmd,env=env,cwd=project,stdout=f,stderr=subprocess.STDOUT,check=True)
if a.mode=='build':
    assert not project.exists();(project/'src').mkdir(parents=True)
    base=Path('/home/dombarker/project-offloads/aspis-r22-svm-20260922-d')
    for n in ['Cargo.toml','Cargo.lock']:shutil.copy2(base/n,project/n)
    original=Path('/home/dombarker/project-offloads/aspis-r20-svm-20260922-a/src/main.rs')
    text=original.read_text();old='[_, _, flag] if flag == "--micro" => true,';assert text.count(old)==1
    text=text.replace(old,'[_, _, _, flag] if flag == "--micro" => true,')
    (project/'src/main.rs').write_text(text)
    run(project/'compile.log',['/home/dombarker/.cargo/bin/cargo','build','--release','--offline','--locked','--jobs','2','--manifest-path',str(project/'Cargo.toml')])
    binary=project/'r24-trace';shutil.copy2(Path(env['CARGO_TARGET_DIR'])/'release/aspis-r17-svm-probe',binary)
    (project/'build.json').write_text(json.dumps({'original_driver_source_sha256':sha(original),'source_sha256':sha(project/'src/main.rs'),'driver_sha256':sha(binary),'change':'enable cached tracing dependency, fix four-argument micro selector; same transaction'},indent=2)+'\n')
else:
    meta=json.loads((project/'build.json').read_text());assert meta['driver_sha256']==sha(project/'r24-trace')
    manifest=json.loads((s/'r18-stage.json').read_text())
    for n,h in manifest['files'].items():assert sha(s/n)==h,n
    build=json.loads((s/'r24-sbf-a/environment.json').read_text());elf=s/'sbf-primary/aspis_v8_performance_sbf.so'
    assert build['elf_sha256']==sha(elf) and build['source_manifest_sha256']==sha(s/'r18-stage.json')
    out=s/'full-trace';assert not out.exists();out.mkdir()
    env['SBF_TRACE_DIR']=str(out/'registers')
    fixture=a.fixture or Path('/home/dombarker/project-offloads/aspis-r19-channel-20260921-c/host-c/fixture-world0')
    clean_receipt=json.loads((s/'r24-svm-a/receipt.json').read_text())
    if a.fixture:
        # A versioned profile must trace its own exact, previously measured proof.
        assert clean_receipt['source_manifest_sha256']==sha(s/'r18-stage.json')
        assert clean_receipt['elf_sha256']==sha(elf)
        assert clean_receipt['runs'][0]['proof_sha256']==sha(fixture/'proof-1.bin')
    run(out/'run.log',[str(project/'r24-trace'),str(elf),str(fixture),'--micro'])
    rows=[json.loads(l)for l in (out/'run.log').read_text().splitlines()if l.startswith('{')];assert len(rows)==1 and rows[0]['accepted']
    clean=clean_receipt['runs'][0]['results']
    assert rows[0]['cu']==next(x['cu']for x in clean if x['case']=='honest' and x['cu_limit']==100000000)
    (out/'receipt.json').write_text(json.dumps({'elf_sha256':sha(elf),'driver':meta,'source_manifest_sha256':sha(s/'r18-stage.json'),'fixture':str(fixture),'proof_sha256':sha(fixture/'proof-1.bin'),'result':rows[0],'clean_cu_equal':True},indent=2)+'\n')
    print(json.dumps({'accepted':True,'cu':rows[0]['cu'],'clean_cu_equal':True}))
