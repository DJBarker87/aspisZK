#!/usr/bin/env python3
"""Export compact source/test evidence from the bounded R56 build workspace."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
out=a.output;assert not out.exists();out.mkdir(parents=True)
base=Path('/home/dombarker/project-offloads');src=base/'aspis-r20-r56-partial-product-20260929-a'
control=base/'aspis-r20-r55-decode-marker-20260929-a'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(s,d):
    assert s.is_file() and 'keypair' not in str(s)
    d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(s,d)
m=json.loads((src/'r18-stage.json').read_text());parent=json.loads((control/'r18-stage.json').read_text())
assert len(m['files'])==188
for n,h in m['files'].items():
    assert sha(src/n)==h,n
    if parent['files'].get(n)!=h:copy(src/n,out/'source'/n)
copy(src/'r18-stage.json',out/'r18-stage.json')
for folder in ['r24-host-a','r24-sbf-a','r24-svm-a']:
    for f in (src/folder).rglob('*'):
        if f.is_file() and f.suffix in ('.log','.json'):copy(f,out/folder/f.relative_to(src/folder))
for n in ['receipt.json','analysis.json','run.log']:copy(src/'full-trace'/n,out/'full-trace'/n)
for letter in ['a','b']:
    for n in ['PartialProduct.log','metadata.json']:copy(base/f'aspis-r56-lean-20260929-{letter}'/n,out/f'lean-{letter}'/n)
print(json.dumps({'output':str(out),'files':sum(f.is_file()for f in out.rglob('*'))}))
