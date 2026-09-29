#!/usr/bin/env python3
"""Collect finite-grid proofs, exhaustive roots, and scripted source-control tests."""
import argparse,hashlib,json,shutil
from fractions import Fraction
from math import prod
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();out=a.output;assert not out.exists();out.mkdir();parent=Path('/home/dombarker/project-offloads')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(src,n):
    assert src.is_file() and 'keypair'not in str(src);dst=out/n;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
control=parent/'aspis-r40-generator-20260929-d';roots=parent/'aspis-r42-roots-20260929-a';stage=parent/'aspis-r42-control-20260929-b'
manifests=[]
for name,src in [('control',control),('roots',roots),('query',stage)]:
    m=json.loads((src/'r18-stage.json').read_text());manifests.append(m)
    for n,h in m['files'].items():assert sha(src/n)==h,n
    copy(src/'r18-stage.json',name+'/r18-stage.json')
    if name!='control':
        for f in(src/'check-a').glob('*'):
            if f.suffix in ['.json','.log']:copy(f,name+'/'+f.name)
old=manifests[0]['files'];new=manifests[-1]['files'];cargo='docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml'
for n,h in old.items():
    if n!=cargo:assert new[n]==h,n
assert len(old)==195 and len(new)==197
assert (stage/cargo).read_bytes().startswith((control/cargo).read_bytes())
selected=['crates/aspis-core/src/'+n for n in ['circle_fri.rs','params.rs','field.rs','transcript.rs']]
selected+=['crates/aspis-core/build.rs',cargo]
for n in selected:
    if n!=cargo:assert sha(control/n)==sha(roots/n)==sha(stage/n),n
    copy(stage/n,'source/'+n)
for letter in 'ab':
    for f in(parent/f'aspis-r42-lean-20260929-{letter}').glob('*'):
        if f.suffix in ['.json','.log']:copy(f,'lean-'+letter+'/'+f.name)
n=262144;distinct=Fraction(prod(n-i for i in range(22)),n**22);bound=Fraction(1105,n)/distinct
(out/'receipt.json').write_text(json.dumps({'parent_revision':'10751450ff23b5c2316b8e220f95a65f6b875ea5','base_source_pins':195,'final_source_pins':197,'new_lean_declarations':6,'root_count':n,'source_checks':{'first_hit':43,'failure':21,'early_return':5,'extra_detection':5,'next_block':43},'inspected_source_sha256':{n:sha(stage/n)for n in selected},'lean_scope':{'MemoryHigh':'3G','MemoryMax':'5G','MemorySwapMax':0,'TasksMax':128},'rust_scope':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128},'ideal_query_distinct_fraction':[distinct.numerator,distinct.denominator],'ideal_query_only_conditioned_bound':[bound.numerator,bound.denominator],'source_distribution_bound':False,'full_privacy':False,'verifier_changed':False,'new_sbf_measurement':False},indent=2)+'\n')
(out/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(out)):sha(f)for f in sorted(out.rglob('*'))if f.is_file()},indent=2)+'\n');print(json.dumps({'artifacts':len(json.loads((out/'MANIFEST.json').read_text())),'source_pins':len(new)}))
