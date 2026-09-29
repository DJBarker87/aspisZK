#!/usr/bin/env python3
"""Collect compact evidence only; never export binaries, accounts or keys."""
import argparse, hashlib, json, shutil
from pathlib import Path

p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
out=a.output;assert not out.exists();out.mkdir(parents=True)
base=Path('/home/dombarker/project-offloads')
control=base/'aspis-r20-shared-blocks-20260928-a'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(src,dst):
    assert src.is_file() and 'keypair' not in str(src)
    dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
parent=json.loads((control/'r18-stage.json').read_text())
for n,h in parent['files'].items():assert sha(control/n)==h,n
for label,folder in [('buffer','aspis-r20-r55-decode-into-20260929-a'),
                     ('marker','aspis-r20-r55-decode-marker-20260929-a')]:
    src=base/folder;dst=out/label
    m=json.loads((src/'r18-stage.json').read_text())
    assert len(m['files'])==183
    for n,h in m['files'].items():assert sha(src/n)==h,n
    copy(src/'r18-stage.json',dst/'r18-stage.json')
    for n,h in m['files'].items():
        if parent['files'].get(n)!=h:copy(src/n,dst/'source'/n)
    for part in ['r24-host-a','r24-sbf-a','r24-svm-a']:
        for f in (src/part).rglob('*'):
            if f.is_file() and f.suffix in ('.log','.json'):copy(f,dst/part/f.relative_to(src/part))
    if label=='marker':
        for n in ['receipt.json','analysis.json','run.log']:copy(src/'full-trace'/n,dst/'full-trace'/n)
for letter in ['a','b']:
    src=base/f'aspis-r55-lean-20260929-{letter}'
    for n in ['PackedCanonicalMarker.log','metadata.json']:
        if (src/n).exists():copy(src/n,out/f'lean-{letter}'/n)
copy(control/'docs/research/v8-no-work-100-20260907/experiments/query_arithmetic.rs',
     out/'control/query_arithmetic.rs')
print(json.dumps({'output':str(out),'files':sum(f.is_file()for f in out.rglob('*'))}))
