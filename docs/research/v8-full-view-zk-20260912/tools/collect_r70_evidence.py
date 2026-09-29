#!/usr/bin/env python3
"""Collect only public focused Lean logs and source/dependency metadata."""
import argparse, json, shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
assert not a.output.exists();a.output.mkdir(parents=True)
base=Path('/home/dombarker/project-offloads')
folders={'final':'aspis-r70-final-20260929-a'}
folders.update({f'word-{c}':f'aspis-r70-word-20260929-{c}' for c in 'ab'})
folders.update({f'product-{c}':f'aspis-r70-product-20260929-{c}' for c in 'abcdefgh'})
for name,folder in folders.items():
    src=base/folder;assert src.is_dir(),src
    dst=a.output/name;dst.mkdir()
    for f in src.iterdir():
        if f.is_file() and f.suffix in ('.json','.log'):shutil.copy2(f,dst/f.name)
print(json.dumps({'folders':folders,'private_fixtures_collected':False,'wallet_keys_collected':False}))
