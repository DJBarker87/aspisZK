#!/usr/bin/env python3
"""Collect focused source/inverse receipts, preserving development failures."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);p.add_argument('--lean',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();out=a.output
assert not out.exists();out.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(src,n):
    assert src.is_file()and'keypair'not in str(src);dst=out/n;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
m=json.loads((a.stage/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(a.stage/n)==h,n
copy(a.stage/'r18-stage.json','r18-stage.json');copy(a.stage/'r17-stage.json','r17-stage.json')
ex='docs/research/v8-no-work-100-20260907/experiments/'
for n in ['r31_sparse_g_inverse.rs','r28_source_helpers.rs','r16_basis_transport.rs','r17_structured_g.rs','r18_sparse_coded_g.rs','performance-host/Cargo.toml']:copy(a.stage/(ex+n),'source/'+ex+n)
for f in (a.stage/'check-a').rglob('*'):
    if f.is_file()and f.suffix in['.json','.log']:copy(f,'runtime/'+str(f.relative_to(a.stage/'check-a')))
for f in a.lean.glob('*'):
    if f.suffix in['.json','.log']:copy(f,'lean/'+f.name)
parent=Path('/home/dombarker/project-offloads')
for letter in 'abcd':
    folder=parent/f'aspis-r31-lean-20260928-{letter}'
    for f in folder.glob('*'):
        if f.suffix in['.json','.log']:copy(f,'development/lean-'+letter+'/'+f.name)
copy(parent/'aspis-r31-inverse-20260928-a/check-a/compile.log','development/rust-a/compile.log')
(out/'receipt.json').write_text(json.dumps({'parent_revision':'331866cfbe3269add68e9ce7c8e050a5e96fdfaa','stage':str(a.stage),'source_manifest_sha256':sha(a.stage/'r18-stage.json'),'pins':len(m['files']),'rust_scope':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128},'lean_scope':{'MemoryHigh':'2G','MemoryMax':'3G','MemorySwapMax':0,'TasksMax':128},'algebraic_witness_only':True,'normalized_witness_sampler_excluded':True,'verifier_changed':False,'full_privacy':False},indent=2)+'\n')
(out/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(out)):sha(f)for f in sorted(out.rglob('*'))if f.is_file()},indent=2)+'\n')
print(json.dumps({'artifacts':len(json.loads((out/'MANIFEST.json').read_text())),'source_pins':len(m['files'])}))
