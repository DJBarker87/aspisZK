#!/usr/bin/env python3
"""Collect public QM31 observer composition receipts, including failed checks."""
import argparse, hashlib, json, shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
assert not a.output.exists();a.output.mkdir(parents=True)
base=Path('/home/dombarker/project-offloads')
folders={n:f'aspis-r80-{n}-20260929-a' for n in ['bridge','challenge','final']}
for kind,suffixes in [('loop','ab'),('limbs','abcd'),('writeback','abc'),('program','ab')]:
    folders.update({f'{kind}-{s}':f'aspis-r80-{kind}-20260929-{s}' for s in suffixes})
for name,folder in folders.items():
    dst=a.output/name;dst.mkdir()
    for f in (base/folder).iterdir():
        if f.is_file() and f.suffix in ['.json','.log']:shutil.copy2(f,dst/f.name)
deps=json.loads((a.output/'final/dependency-pins.json').read_text())
for path,h in deps.items():assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==h,path
(a.output/'collection.json').write_text(json.dumps({'dependency_pins_verified':len(deps),
    'private_fixtures_collected':False,'wallet_keys_collected':False},indent=2)+'\n')
print(json.dumps({'files':sum(f.is_file()for f in a.output.rglob('*'))}))
