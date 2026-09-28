#!/usr/bin/env python3
"""Validate and retain small source/measurement artifacts, never wallet keys."""
import argparse,difflib,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser()
for n in ['control','native','full','output']:p.add_argument('--'+n,type=Path,required=True)
a=p.parse_args();assert not a.output.exists();a.output.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(src,n):
    dst=a.output/n;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
for label,stage,count in [('native',a.native,182),('full',a.full,174)]:
    m=json.loads((stage/'r18-stage.json').read_text());assert len(m['files'])==count
    for n,h in m['files'].items():assert sha(stage/n)==h,n
    for n in ['r18-stage.json','r17-stage.json','r17-sbf-probe.json']:copy(stage/n,label+'/'+n)
    assert m['r23_width']['original_field_sha256']==sha(a.control/'crates/aspis-core/src/field.rs')
for n in ['host/compile.log','host/check.log','host/metadata.json','host/generated/world0.bin','host/generated/world1.bin','sbf/compile.log','sbf/metadata.json','svm/receipt.json','trace-analysis.json','r23-width-analysis.json']:
    copy(a.native/n,'native/'+n)
for mode in ['reference','scalar']:
    for world in range(2):
        for n in ['svm.jsonl','time.txt']:copy(a.native/f'svm/{mode}-world{world}'/n,f'native/svm/{mode}-world{world}/{n}')
    for n in ['svm.jsonl','time.txt']:copy(a.native/f'trace/{mode}-world0'/n,f'native/trace/{mode}-world0/{n}')
for mode in ['host','sbf','svm']:
    src=a.full/f'r23-{mode}-a'
    for f in src.rglob('*'):
        if f.is_file() and f.suffix in ['.log','.json'] and 'synthetic-only' not in f.parts:copy(f,'full/'+str(f.relative_to(a.full)))
copy(a.full/'r23-host/compile.log','full/host-preflight-wrong-bin.log')
copy(a.native.parent/'r23-callers-20260928.json','original-callers.json')
old=(a.control/'crates/aspis-core/src/field.rs').read_text();new=(a.full/'crates/aspis-core/src/field.rs').read_text()
(a.output/'field.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='R20/field.rs',tofile='R23/field.rs')))
copy(a.full/'crates/aspis-core/src/r23_width.rs','r23_width.rs')
host=(a.native/'host/check.log').read_text();assert 'random_pairs=200000 boundary_pairs=1296' in host and 'checked_overflow_panics=15' in host
assert 'R22_NATIVE source_vectors=256 adjoint_basis_cases=4096 genuine_public_inputs=2' in host
controls=json.loads((a.full/'r23-host-a/wire-controls/results.json').read_text());assert len(controls['cases'])==3281
for w in range(2):assert 'R17_PUBLIC_PREFIX_ACCEPTED' in (a.full/f'r23-host-a/world{w}.log').read_text()
r=json.loads((a.full/'r23-svm-a/receipt.json').read_text());assert r['elf_sha256']==sha(a.full/'sbf-primary/aspis_v8_performance_sbf.so')
summary={'control_revision':'6f00e7f6c893c3a81bc37526e32d563434d303c8','research_base':'fbd5e9ac362b16713f828c1a1508af497d5d9e6d','native_stage':str(a.native),'full_stage':str(a.full),'source_sites_changed':2,'overflow_checks_retained':True,'scalar_transpose_in_full_verifier':False,'full_privacy_or_soundness_proved':False,'launch_limits':{'build':'MemoryHigh=5G MemoryMax=7G MemorySwapMax=0 TasksMax=128','runtime':'MemoryHigh=2G MemoryMax=3G MemorySwapMax=0 TasksMax=128'},'host_compile_environment':{'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true'},'full_runs':[]}
for run,oldcu in zip(r['runs'],[2865333,2866803]):
    honest=[x for x in run['results']if x['case']=='honest'];high=next(x for x in honest if x['cu_limit']==100000000);low=next(x for x in honest if x['cu_limit']==1000000)
    assert high['accepted']
    summary['full_runs'].append({'world':run['world'],'old_cu':oldcu,'new_cu':high['cu'],'saving':oldcu-high['cu'],'one_million_accepted':low['accepted'],'one_million_resource_failure':low['resource_failure']})
(a.output/'receipt.json').write_text(json.dumps(summary,indent=2)+'\n')
(a.output/'MANIFEST.json').write_text(json.dumps({str(p.relative_to(a.output)):sha(p)for p in sorted(a.output.rglob('*'))if p.is_file()},indent=2)+'\n')
print(json.dumps(summary,indent=2))
