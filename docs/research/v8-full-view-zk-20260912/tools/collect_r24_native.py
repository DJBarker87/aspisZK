#!/usr/bin/env python3
"""Retain exact research sources and compact receipts; never copy account keys."""
import argparse,difflib,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();out=a.output
assert not out.exists();out.mkdir()
base=Path('/home/dombarker/project-offloads')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(src,dst):
    assert 'keypair' not in src.name
    target=out/dst;target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,target)
stages={
 'compose-a':'aspis-r20-compose-20260928-a','compose-b':'aspis-r20-compose-20260928-b',
 'compose-c':'aspis-r20-compose-20260928-c','profile-b':'aspis-r20-profile-20260928-b',
 'qm-a-rejected':'aspis-r22-qm-20260928-a','qm-b-rejected':'aspis-r22-qm-20260928-b',
 'qm-c':'aspis-r22-qm-20260928-c','inactive-a':'aspis-r22-inactive-20260928-a',
 'addsub-a-rejected':'aspis-r22-addsub-20260928-a','addsub-b-rejected':'aspis-r22-addsub-20260928-b',
 'addsub-c-rejected':'aspis-r22-addsub-20260928-c','packed-a-slower':'aspis-r22-packed-20260928-a'}
summary={'source_base_revision':'a0f2d200c295f3028a12e1142a39a026d19bf1a0','full_privacy_or_soundness_proved':False,'stages':{}}
control=base/'aspis-r20-width-20260928-a'
for label,name in stages.items():
    stage=base/name;m=json.loads((stage/'r18-stage.json').read_text())
    for n,h in m['files'].items():assert sha(stage/n)==h,n
    copy(stage/'r18-stage.json',label+'/r18-stage.json')
    summary['stages'][label]={'path':str(stage),'pins':len(m['files']),'source_manifest_sha256':sha(stage/'r18-stage.json'),'rejected':'rejected' in label or 'slower' in label}
    for folder in ['host','sbf','svm','r24-host-a','r24-sbf-a','r24-svm-a']:
        if not(stage/folder).exists():continue
        for f in sorted((stage/folder).rglob('*')):
            if f.is_file() and f.suffix in ['.log','.json','.jsonl','.txt'] and 'keypair' not in f.name:
                copy(f,label+'/'+str(f.relative_to(stage)))
    if 'r24_compose' in m:
        r=json.loads((stage/'r24-svm-a/receipt.json').read_text())
        assert r['elf_sha256']==sha(stage/'sbf-primary/aspis_v8_performance_sbf.so')
        summary['stages'][label]['instrumented']='r24_profile' in m
        summary['stages'][label]['full_cu']=[next(x['cu']for x in w['results']if x['case']=='honest' and x['cu_limit']==100000000)for w in r['runs']]
        if 'r24_profile' not in m:
            checks=json.loads((stage/'r24-host-a/wire-controls/results.json').read_text())
            assert len(checks['cases'])==3281 and sum(x['checked_rejection']for x in checks['cases'])==3280
    if label in ['qm-c','inactive-a','packed-a-slower']:
        assert (stage/'sbf/metadata.json').exists()
        log=(stage/'sbf/compile.log').read_text();assert 'overflows the maximum allowed frame' not in log
        assert not('Stack offset' in log and 'exceeded' in log)
        assert 'source_vectors=256 adjoint_basis_cases=4096 genuine_public_inputs=2' in (stage/'host/check.log').read_text()
        r=json.loads((stage/'svm/receipt.json').read_text());assert r['elf_sha256']==sha(stage/'sbf/aspis_v8_performance_sbf.so')
    # Exact modified sources (including rejected alternatives), not just descriptions.
    for n in m['files']:
        if not(control/n).exists() or sha(control/n)!=m['files'][n]:
            if Path(n).suffix in ['.rs','.toml']:copy(stage/n,label+'/source/'+n)
for label in ['a','b']:
    stage=base/f'aspis-r24-lean-20260928-{label}'
    for name in ['metadata.json','compile.log']:copy(stage/name,'lean-'+label+'/'+name)
lean=Path(__file__).parent/'R24NativeBounds.lean'
assert sha(lean)==json.loads((base/'aspis-r24-lean-20260928-b/metadata.json').read_text())['source_sha256']
copy(lean,'R24NativeBounds.lean')
summary['best_full_cu']=summary['stages']['compose-c']['full_cu']
summary['one_million_gate']='OPEN: both genuine proofs exhaust at the actual cap'
(out/'receipt.json').write_text(json.dumps(summary,indent=2)+'\n')
(out/'MANIFEST.json').write_text(json.dumps({str(p.relative_to(out)):sha(p)for p in sorted(out.rglob('*'))if p.is_file()},indent=2)+'\n')
print(json.dumps(summary,indent=2))
