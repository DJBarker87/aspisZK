#!/usr/bin/env python3
"""Collect bounded public proof/source receipts; no fixtures or compiled objects."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
out=a.output;assert not out.exists();out.mkdir(parents=True)
base=Path('/home/dombarker/project-offloads')
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def copy(f,to):
    assert f.is_file() and 'keypair' not in str(f)
    to.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(f,to)
def blob(f):
    h=sha(f);dst=out/'blobs'/h
    if not dst.exists():copy(f,dst)
    assert sha(dst)==h;return h
control=base/'aspis-r20-r117-primal-20260930-a'
pm=json.loads((control/'r18-stage.json').read_text())
for n,h in pm['files'].items():assert sha(control/n)==h,n
copy(control/'r18-stage.json',out/'control/r18-stage.json')
source_records={}
for number in [118,119,120]:
    stage=base/f'aspis-r20-r{number}-boundary-20260930-a'
    m=json.loads((stage/'r18-stage.json').read_text());sources={};arts={}
    for n,h in m['files'].items():
        assert sha(stage/n)==h,n
        if pm['files'].get(n)!=h:sources[n]=blob(stage/n)
    assert len(sources)==3
    for f in sorted((stage/'check-a').rglob('*')):
        if f.is_file() and f.suffix in ['.json','.log']:
            arts[str(f.relative_to(stage/'check-a'))]=blob(f)
    dest=out/f'r{number}-source'
    copy(stage/'r18-stage.json',dest/'r18-stage.json')
    (dest/'sources.json').write_text(json.dumps(sources,indent=2)+'\n')
    (dest/'artifacts.json').write_text(json.dumps(arts,indent=2)+'\n')
    source_records[f'r{number}-source']={'stage':str(stage),'pins':len(m['files'])}
formal={}
for folder in ['aspis-r119-augmented-20260930-a','aspis-r119-augmented-20260930-b',
    'aspis-r120-quotient-20260930-a','aspis-r120-quotient-20260930-b',
    'aspis-r120-preflight-20260930-a','aspis-r120-special-20260930-a',
    'aspis-r120-certificate-20260930-a','aspis-r120-bridge-20260930-a',
    'aspis-r120-bridge-20260930-b','aspis-r120-mask-20260930-c',
    'aspis-r120-opening-20260930-a','aspis-r120-release-20260930-a']:
    stage=base/folder;arts={}
    for f in sorted(stage.iterdir()):
        if f.is_file() and f.suffix in ['.json','.log']:arts[f.name]=blob(f)
    formal[folder]={'stage':str(stage),'artifacts':arts}
(out/'formal.json').write_text(json.dumps(formal,indent=2)+'\n')
(out/'collection.json').write_text(json.dumps({'sources':source_records,
    'private_fixtures_collected':False,'compiled_objects_collected':False,
    'wallet_keys_collected':False,'verifier_changed':False},indent=2)+'\n')
print(json.dumps({'files':sum(f.is_file() for f in out.rglob('*')),'output':str(out)}))
