#!/usr/bin/env python3
"""Collect public circle-proof logs and dependency/source metadata only."""
import argparse, json, shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
assert not a.output.exists();a.output.mkdir(parents=True)
base=Path('/home/dombarker/project-offloads')
folders={'final':'aspis-r71-final-20260929-a','scalar':'aspis-r71-scalar-20260929-a',
    'field':'aspis-r71-field-20260929-a','circle-failed':'aspis-r71-circle-20260929-a',
    'circle':'aspis-r71-circle-20260929-b'}
for name,folder in folders.items():
    src=base/folder;assert src.is_dir(),src
    dst=a.output/name;dst.mkdir()
    for f in src.iterdir():
        if f.is_file() and f.suffix in ('.json','.log'):shutil.copy2(f,dst/f.name)
print(json.dumps({'folders':folders,'private_fixtures_collected':False,'wallet_keys_collected':False}))
