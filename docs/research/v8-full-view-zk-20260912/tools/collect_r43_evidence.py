#!/usr/bin/env python3
"""Retain scrutiny, rejected specializations, the boundary fix, and exact proof receipts."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();out=a.output;assert not out.exists();out.mkdir();parent=Path('/home/dombarker/project-offloads')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(src,n):
    assert src.is_file()and'keypair'not in str(src);dst=out/n;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
control=parent/'aspis-r42-control-20260929-b';old=json.loads((control/'r18-stage.json').read_text());copy(control/'r18-stage.json','control/r18-stage.json')
cargo='docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml';ex='docs/research/v8-no-work-100-20260907/experiments/'
for letter in 'abcdefghi':
    stage=parent/f'aspis-r43-query-20260929-{letter}';m=json.loads((stage/'r18-stage.json').read_text());assert len(m['files'])==198
    for n,h in m['files'].items():assert sha(stage/n)==h,n
    for n,h in old['files'].items():
        if n!=cargo:assert m['files'][n]==h,n
    assert(stage/cargo).read_bytes().startswith((control/cargo).read_bytes())
    copy(stage/'r18-stage.json',f'rust-{letter}/r18-stage.json')
    host='r43_query_coverage.rs'if letter<'f'else'r43_universal_witness.rs';copy(stage/ex/host,f'rust-{letter}/'+host)
    for f in(stage/'check-a').rglob('*'):
        if f.is_file()and f.suffix in['.json','.log']:copy(f,f'rust-{letter}/'+str(f.relative_to(stage/'check-a')))
stage=parent/'aspis-r43-query-20260929-i'
for name in ['r17_opening_weights.rs','r17_structured_g.rs','r18_sparse_coded_g.rs']:
    copy(stage/ex/name,'source/'+name)
for letter in 'abcdefgh':
    for f in(parent/f'aspis-r43-lean-20260929-{letter}').glob('*'):
        if f.suffix=='.log' or(f.name=='metadata.json'and letter in'egh'):copy(f,'lean-'+letter+'/'+f.name)
(out/'receipt.json').write_text(json.dumps({'parent_revision':'0ffa62b927c35a499f15e3412cffb643803ab7ca','base_source_pins':197,'per_stage_source_pins':198,'new_lean_declarations':39,'selected_columns':list(range(6,18))+[29],'executed_determinant':2079196465,'low_repair_boundary':88,'omitted_boundary_negative_slots':[2,3,5,6],'lean_scope':{'MemoryHigh':'3G','MemoryMax':'5G','MemorySwapMax':0,'TasksMax':128},'rust_scope':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128},'arbitrary_low_repair_invariance':True,'universal_source_root_theorem':False,'source_distribution_bound':False,'full_privacy':False,'verifier_changed':False,'new_sbf_measurement':False},indent=2)+'\n')
(out/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(out)):sha(f)for f in sorted(out.rglob('*'))if f.is_file()},indent=2)+'\n');print(json.dumps({'artifacts':len(json.loads((out/'MANIFEST.json').read_text()))}))
