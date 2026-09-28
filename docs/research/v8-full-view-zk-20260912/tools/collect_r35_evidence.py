#!/usr/bin/env python3
"""Collect focused formal evidence and verify unchanged R34 source pins."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();out=a.output;assert not out.exists();out.mkdir()
parent=Path('/home/dombarker/project-offloads');stage=parent/'aspis-r34-factor-20260929-a'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((stage/'r18-stage.json').read_text());assert len(m['files'])==189
for n,h in m['files'].items():assert sha(stage/n)==h,n
for letter in 'abc':
    for f in(parent/f'aspis-r35-lean-20260929-{letter}').glob('*'):
        if f.suffix in['.json','.log']:
            dst=out/f'lean-{letter}'/f.name;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(f,dst)
receipt={'parent_revision':'37c3eeb9c831a2cdc3590e4afbbea5ea2b74dee1','source_manifest_sha256':sha(stage/'r18-stage.json'),'unchanged_source_pins':len(m['files']),'new_lean_declarations':13,'lean_scope':{'MemoryHigh':'3G','MemoryMax':'5G','MemorySwapMax':0,'TasksMax':128},'full_privacy':False,'universal_residual_coverage':False,'verifier_changed':False,'new_rust_or_sbf_run':False}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
(out/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(out)):sha(f)for f in sorted(out.rglob('*'))if f.is_file()},indent=2)+'\n')
print(json.dumps({'artifacts':len(json.loads((out/'MANIFEST.json').read_text())),'source_pins':len(m['files'])}))
