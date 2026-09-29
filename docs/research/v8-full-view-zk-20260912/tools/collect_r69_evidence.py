#!/usr/bin/env python3
"""Collect public source deltas and receipts; no wallets or private fixtures."""
import argparse, hashlib, json, shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
out=a.output;assert not out.exists();out.mkdir(parents=True)
base=Path('/home/dombarker/project-offloads')
stage=base/'aspis-r20-r69-explicit-20260929-b'
control=base/'aspis-r20-r62-gather-20260929-b'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(s,d):
    assert s.is_file() and 'keypair' not in str(s)
    d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(s,d)
parent=json.loads((control/'r18-stage.json').read_text())
current=json.loads((stage/'r18-stage.json').read_text())
assert len(parent['files'])==197 and len(current['files'])==202
for src,manifest in [(stage,current),(control,parent)]:
    for name,digest in manifest['files'].items():assert sha(src/name)==digest,name
for name,digest in current['files'].items():
    if parent['files'].get(name)!=digest:copy(stage/name,out/'runtime/source'/name)
copy(stage/'r18-stage.json',out/'runtime/r18-stage.json')
for folder in ['r24-host-a','r24-sbf-a','r24-svm-a']:
    for f in (stage/folder).rglob('*'):
        if f.is_file() and f.suffix in ('.log','.json'):
            copy(f,out/'runtime'/folder/f.relative_to(stage/folder))
for name,folder in [('extraction','aspis-r69-explicit-extracted-20260929-a'),
                    ('chain-a','aspis-r69-chain-20260929-a'),('chain-b','aspis-r69-chain-20260929-b'),
                    ('array-a','aspis-r69-array-20260929-a'),('array-b','aspis-r69-array-20260929-b')]:
    for f in (base/folder).rglob('*'):
        rel=f.relative_to(base/folder)
        if f.is_file() and rel.parts[0]!='target':copy(f,out/name/rel)
for name,folder in [('focused','aspis-r69-lean-20260929-a'),('final','aspis-r69-final-20260929-a')]:
    for f in (base/folder).iterdir():
        if f.is_file() and f.suffix in ('.log','.json'):copy(f,out/name/f.name)
svm=json.loads((stage/'r24-svm-a/receipt.json').read_text())
elf=stage/'sbf-primary/aspis_v8_performance_sbf.so'
assert sha(elf)==svm['elf_sha256']
(out/'collection.json').write_text(json.dumps({
    'base_revision':'265a251ecfbff6cd971a32eccd72cff552786885',
    'source_files_verified':202,'control_files_verified':197,
    'observed_elf_sha256':sha(elf),
    'charon_sha256':sha(base/'ZK-v5-formal/toolchains/charon/bin/charon'),
    'aeneas_sha256':sha(base/'aspis-v7-aeneas-source-unblock-20260830/aeneas-repro-r1'),
    'private_fixtures_collected':False,'wallet_keys_collected':False,
    'new_runtime_stage':str(stage)},indent=2)+'\n')
print(json.dumps({'output':str(out),'files':sum(f.is_file()for f in out.rglob('*'))}))
