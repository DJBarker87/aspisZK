#!/usr/bin/env python3
"""Collect public-only R83 source deltas, successes and failed experiments."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
out=a.output;assert not out.exists();out.mkdir(parents=True)
base=Path('/home/dombarker/project-offloads');control=base/'aspis-r20-r82-dotinline-20260929-a'
variants={'tensor':'tensor-20260929-a','blockdot':'blockdot-20260929-a',
    'packed-failed':'packed-20260929-a','packed':'packed-20260929-b',
    'packed-block':'packed-block-20260929-a','opt2':'opt2-20260929-a'}
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def copy(f,to):
    assert f.is_file() and 'keypair' not in str(f)
    to.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(f,to)
def blob(f):
    h=sha(f);to=out/'blobs'/h
    if not to.exists():copy(f,to)
    assert sha(to)==h;return h
assert sha(control/'r18-stage.json')=='f70d74f4e479899b7eda0664a4dfdf4b8e8068d7bf9be836a2cd681397167498'
pm=json.loads((control/'r18-stage.json').read_text())
for n,h in pm['files'].items():assert sha(control/n)==h,n
copy(control/'r18-stage.json',out/'control/r18-stage.json')
copy(control/'r24-svm-a/receipt.json',out/'control/svm.json')
original={};collections={}
for variant,suffix in variants.items():
    stage=base/('aspis-r20-r83-'+suffix);d=out/variant
    m=json.loads((stage/'r18-stage.json').read_text());sources={}
    for n,h in m['files'].items():
        assert sha(stage/n)==h,n
        if pm['files'].get(n)!=h:
            sources[n]=blob(stage/n)
            if (control/n).exists():original[n]=blob(control/n)
    copy(stage/'r18-stage.json',d/'r18-stage.json')
    (d/'sources.json').write_text(json.dumps(sources,indent=2)+'\n')
    arts={}
    for mode in ['host','sbf','svm']:
        folder=stage/f'r24-{mode}-a'
        if not folder.exists():continue
        for f in sorted(folder.iterdir()):
            if f.is_file() and f.suffix in ['.log','.json']:arts[f'r24-{mode}-a/{f.name}']=blob(f)
        if (folder/'wire-controls/results.json').exists():arts['wire-controls.json']=blob(folder/'wire-controls/results.json')
    if (stage/'host-reuse.json').exists():arts['host-reuse.json']=blob(stage/'host-reuse.json')
    (d/'artifacts.json').write_text(json.dumps(arts,indent=2)+'\n')
    svm=stage/'r24-svm-a/receipt.json';digest=None
    if svm.exists():
        digest=json.loads(svm.read_text())['elf_sha256']
        assert sha(stage/'sbf-primary/aspis_v8_performance_sbf.so')==digest
    collections[variant]={'stage':str(stage),'pins':len(m['files']),'elf_sha256':digest}
(out/'control/sources.json').write_text(json.dumps(original,indent=2)+'\n')
(out/'collection.json').write_text(json.dumps({'base_revision':'d137f7316e0878bfb90780c13214a7586287deb2','variants':collections,
    'private_fixtures_collected':False,'wallet_keys_collected':False,'ELFs_collected':False},indent=2)+'\n')
print(json.dumps({'output':str(out),'files':sum(f.is_file()for f in out.rglob('*'))}))
