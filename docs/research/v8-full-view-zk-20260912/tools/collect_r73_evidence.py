#!/usr/bin/env python3
"""Collect public squeeze-source proof receipts only."""
import argparse, hashlib, json, shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
assert not a.output.exists();a.output.mkdir(parents=True)
base=Path('/home/dombarker/project-offloads')
folders={'final':'aspis-r73-final-20260929-a'}
folders.update({f'{kind}-{suffix}':f'aspis-r73-{kind}-20260929-{suffix}'
    for kind in ['squeeze','bridge']for suffix in 'abc'})
for name,folder in folders.items():
    dst=a.output/name;dst.mkdir()
    for f in (base/folder).iterdir():
        if f.is_file()and f.suffix in ['.json','.log']:shutil.copy2(f,dst/f.name)
deps=json.loads((a.output/'final/dependency-pins.json').read_text())
for path,h in deps.items():assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==h,path
(a.output/'collection.json').write_text(json.dumps({'dependency_pins_verified':len(deps),
    'private_fixtures_collected':False,'wallet_keys_collected':False},indent=2)+'\n')
print(json.dumps({'files':sum(f.is_file()for f in a.output.rglob('*'))}))
