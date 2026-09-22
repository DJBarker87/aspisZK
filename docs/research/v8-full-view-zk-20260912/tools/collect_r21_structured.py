#!/usr/bin/env python3
"""Retain measured specialized-pilot evidence without copying keys or binaries."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
a=p.parse_args();assert not a.output.exists();a.output.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(name):
    dest=a.output/name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(a.stage/name,dest)
m=json.loads((a.stage/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(a.stage/n)==h,n
for n in ['r17-stage.json','r17-sbf-probe.json','r18-stage.json','r21-stage.json','sbf-build.log']:copy(n)
assert 'Exit status: 0' in (a.stage/'sbf-build.log').read_text()
ex=Path('docs/research/v8-no-work-100-20260907/experiments')
for n in ['r21_gkr.rs','r21_pilot.rs']:
    (a.output/'assembled').mkdir(exist_ok=True);shutil.copy2(a.stage/ex/n,a.output/'assembled'/n)
elf=a.stage/'sbf-primary/aspis_v8_performance_sbf.so'
receipt={'scope':'ordinary+image ONLY','complete_aspis_verifier':False,'full_privacy_proved':False,
    'source_refinement_proved':False,'fiat_shamir_soundness_proved':False,
    'source_pins_checked':len(m['files']),'source_manifest_sha256':sha(a.stage/'r18-stage.json'),
    'elf_sha256':sha(elf),'stage':str(a.stage),'circuit':m['r21_circuit']['profile'],'worlds':[]}
for w in range(2):
    host=f'host-world{w}';svm=f'svm-world{w}'
    for n in ['compile.log','pilot.log','metadata.json','context.bin','generated/helper.bin']:copy(f'{host}/{n}')
    for n in ['metadata.json','svm.jsonl','time.txt']:copy(f'{svm}/{n}')
    log=(a.stage/host/'pilot.log').read_text()
    assert all(s in log for s in ['R21_STRUCTURED_WIRING checks=1088','R21_SOURCE_DIFF cases=160','tampered_message_fields=1247','Exit status: 0'])
    metadata=json.loads((a.stage/svm/'metadata.json').read_text())
    assert metadata['elf_sha256']==sha(elf) and metadata['wire_sha256']==sha(a.stage/host/'generated/helper.bin')
    rows=[json.loads(l)for l in (a.stage/svm/'svm.jsonl').read_text().splitlines()]
    assert len(rows)==20 and all(r['heap_bytes']==262144 and not r['complete_aspis_verifier'] for r in rows)
    honest=[r for r in rows if r['case']=='honest'];high=next(r for r in honest if r['cu_limit']==100000000);low=next(r for r in honest if r['cu_limit']==1000000)
    assert high['accepted'] and low['resource_failure'] and not low['accepted'] and not low['checked_rejection']
    negatives=[r for r in rows if r['case']!='honest'];assert all(not r['accepted'] for r in negatives)
    assert all(r['checked_rejection'] and not r['resource_failure'] for r in negatives if r['cu_limit']==100000000)
    receipt['worlds'].append({'complete_helper_cu':high['cu'],'one_million_cap_passed':False,
        'negative_checked':sum(r['checked_rejection'] for r in negatives),'negative_resource_failures':sum(r['resource_failure'] for r in negatives)})
receipt['decision']='REJECT integration: specialized helper remains more expensive than native'
receipt['launch_limits']={'build':'MemoryHigh=5G MemoryMax=7G MemorySwapMax=0 TasksMax=128','svm':'MemoryHigh=2G MemoryMax=3G MemorySwapMax=0 TasksMax=128'}
(a.output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
manifest={str(f.relative_to(a.output)):sha(f) for f in sorted(a.output.rglob('*')) if f.is_file()}
(a.output/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='circuit'},indent=2))
