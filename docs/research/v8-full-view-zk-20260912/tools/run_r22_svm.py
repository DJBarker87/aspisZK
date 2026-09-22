#!/usr/bin/env python3
"""Bounded release SVM runner with optional executed-register capture."""
import argparse,hashlib,json,os,shutil,subprocess,tomllib
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--project',type=Path,required=True);p.add_argument('--stage',type=Path,required=True);p.add_argument('--wires',type=Path,required=True);p.add_argument('--trace',action='store_true')
a=p.parse_args();here=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
binary=a.project/'r22-svm';env=dict(os.environ,NO_DNA='1',PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-svm/target')
if not binary.exists():
    assert not a.project.exists();(a.project/'src').mkdir(parents=True)
    base=Path('/home/dombarker/project-offloads/aspis-r20-svm-20260922-a')
    shutil.copy2(base/'Cargo.lock',a.project/'Cargo.lock')
    text=(base/'Cargo.toml').read_text().replace('litesvm = "=0.16.0"','litesvm = {version="=0.16.0",features=["register-tracing"]}')
    (a.project/'Cargo.toml').write_text(text);shutil.copy2(here/'r22_svm.rs',a.project/'src/main.rs')
    # Enable cached optional tracing dependencies without changing any locked
    # baseline package version/checksum. No program dependency is changed.
    def packages(path):
        return {(x['name'],x['version'],x.get('source'),x.get('checksum')) for x in tomllib.loads(path.read_text())['package']}
    old=packages(base/'Cargo.lock')
    with (a.project/'resolution.stdout').open('w')as f,(a.project/'resolution.log').open('w')as e:
        subprocess.run(['/home/dombarker/.cargo/bin/cargo','update','--offline','--package','litesvm','--precise','0.16.0','--manifest-path',str(a.project/'Cargo.toml')],env=env,cwd=a.project,stdout=f,stderr=e,check=True)
    new=packages(a.project/'Cargo.lock');assert old<=new,'refuse baseline package replacement'
    (a.project/'added-tracing-packages.json').write_text(json.dumps(sorted(new-old),indent=2)+'\n')
    cmd=['/usr/bin/time','-v','/home/dombarker/.cargo/bin/cargo','build','--release','--offline','--locked','--jobs','2','--manifest-path',str(a.project/'Cargo.toml')]
    with (a.project/'compile.log').open('w')as f:subprocess.run(cmd,env=env,cwd=a.project,stdout=f,stderr=subprocess.STDOUT,check=True)
    shutil.copy2(Path(env['CARGO_TARGET_DIR'])/'release/aspis-r17-svm-probe',binary)
out=a.stage/('trace' if a.trace else 'svm');assert not out.exists();out.mkdir()
elf=a.stage/'sbf/aspis_v8_performance_sbf.so';receipt={'elf_sha256':sha(elf),'driver_sha256':sha(binary),'driver_source_sha256':sha(a.project/'src/main.rs'),'scope':'native ordinary+image ONLY','runs':[]}
for w in (range(1) if a.trace else range(2)):
    wire=a.wires/f'world{w}.bin'
    for mode in ['reference','scalar']:
        dest=out/f'{mode}-world{w}';dest.mkdir();runenv=dict(env)
        if a.trace:runenv['SBF_TRACE_DIR']=str(dest/'registers')
        else:runenv.pop('SBF_TRACE_DIR',None)
        with (dest/'svm.jsonl').open('w')as f,(dest/'time.txt').open('w')as t:
            subprocess.run(['/usr/bin/time','-v',str(binary),str(elf),str(wire),mode],env=runenv,cwd=a.project,stdout=f,stderr=t,check=True)
        rows=[json.loads(l)for l in (dest/'svm.jsonl').read_text().splitlines()]
        assert all(r['accepted'] if r['case']=='honest' else r['checked_rejection'] and not r['resource_failure'] for r in rows)
        receipt['runs'].append({'world':w,'mode':mode,'wire_sha256':sha(wire),'results':rows})
        for r in rows:
            if r['case']=='honest':print(json.dumps(r),flush=True)
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
