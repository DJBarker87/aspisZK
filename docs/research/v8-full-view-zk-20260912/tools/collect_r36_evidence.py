#!/usr/bin/env python3
"""Collect public source-model comparisons, pinned tables and formal receipts."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();out=a.output;assert not out.exists();out.mkdir();parent=Path('/home/dombarker/project-offloads')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(src,n):
    assert src.is_file()and'keypair'not in str(src);dst=out/n;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
m=json.loads((a.stage/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(a.stage/n)==h,n
copy(a.stage/'r18-stage.json','r18-stage.json');copy(a.stage/'r17-stage.json','r17-stage.json');ex='docs/research/v8-no-work-100-20260907/experiments/'
for n in['r36_residual_model.rs','r17_basis_tables.rs','performance-host/Cargo.toml']:copy(a.stage/(ex+n),'source/'+ex+n)
for f in(a.stage/'check-a').rglob('*'):
    if f.is_file()and f.suffix in['.json','.log','.lean','.bin']:copy(f,'runtime/'+str(f.relative_to(a.stage/'check-a')))
for w in range(2):copy(a.stage/f'world{w}-prefix.bin',f'prefix/world{w}.bin')
for letter in 'abcd':
    for f in(parent/f'aspis-r36-lean-20260929-{letter}').glob('*'):
        if f.suffix in['.json','.log']:copy(f,'lean-'+letter+'/'+f.name)
(out/'receipt.json').write_text(json.dumps({'parent_revision':'998ff7a2a200a054b65b1f9fbbc54345f90dba9b','stage':str(a.stage),'source_manifest_sha256':sha(a.stage/'r18-stage.json'),'source_pins':len(m['files']),'new_lean_declarations':16,'rust_scope':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128},'lean_scope':{'MemoryHigh':'3G','MemoryMax':'5G','MemorySwapMax':0,'TasksMax':128},'actual_prefixes':2,'source_prefix_substituted':False,'full_privacy':False,'universal_residual_coverage':False,'verifier_changed':False},indent=2)+'\n')
(out/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(out)):sha(f)for f in sorted(out.rglob('*'))if f.is_file()},indent=2)+'\n');print(json.dumps({'artifacts':len(json.loads((out/'MANIFEST.json').read_text())),'source_pins':len(m['files'])}))
