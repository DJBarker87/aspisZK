#!/usr/bin/env python3
"""Retain R91 arithmetic/stack attempts and focused query-loop evidence."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
out=a.output;assert not out.exists();out.mkdir(parents=True);base=Path('/home/dombarker/project-offloads')
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def copy(f,to):
    assert f.is_file()and 'keypair'not in str(f)
    to.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(f,to)
def blob(f):
    h=sha(f);to=out/'blobs'/h
    if not to.exists():copy(f,to)
    assert sha(to)==h;return h
control=base/'aspis-r20-r90-gamma-20260929-a';pm=json.loads((control/'r18-stage.json').read_text())
for n,h in pm['files'].items():assert sha(control/n)==h,n
copy(control/'r18-stage.json',out/'control/r18-stage.json');original={};records={}
for suffix in 'abcde':
    variant='wide-'+suffix;stage=base/f'aspis-r20-r91-wide-20260929-{suffix}'
    m=json.loads((stage/'r18-stage.json').read_text());sources={};arts={}
    for n,h in m['files'].items():
        assert sha(stage/n)==h,n
        if pm['files'].get(n)!=h:
            sources[n]=blob(stage/n)
            if n in pm['files']:original[n]=blob(control/n)
    d=out/variant;copy(stage/'r18-stage.json',d/'r18-stage.json')
    for name in ['r24-host-a','r24-sbf-a','r24-svm-a','r91-recorder']:
        folder=stage/name
        if not folder.exists():continue
        for f in sorted(folder.iterdir()):
            if f.is_file()and f.suffix in ['.json','.log']:arts[name+'/'+f.name]=blob(f)
        if(folder/'wire-controls/results.json').exists():arts['wire-controls.json']=blob(folder/'wire-controls/results.json')
    (d/'sources.json').write_text(json.dumps(sources,indent=2)+'\n')
    (d/'artifacts.json').write_text(json.dumps(arts,indent=2)+'\n')
    records[variant]={'stage':str(stage),'pins':len(m['files'])}
formal=[*(f'query-block-{s}'for s in 'abcdef'),'query-step-a','query-loop-a','query-loop-b','query-final-a']
for n in formal:
    kind,suffix=n.rsplit('-',1);folder=base/f'aspis-r91-{kind}-20260929-{suffix}'
    for f in folder.iterdir():
        if f.is_file()and f.suffix in ['.json','.log']:copy(f,out/'lean'/n/f.name)
deps=json.loads((out/'lean/query-final-a/dependency-pins.json').read_text())
for n,h in deps.items():assert sha(Path(n))==h,n
(out/'control/sources.json').write_text(json.dumps(original,indent=2)+'\n')
(out/'collection.json').write_text(json.dumps({'variants':records,'formal_dependency_pins_verified':len(deps),
 'private_fixtures_collected':False,'ELFs_collected':False,'wallet_keys_collected':False},indent=2)+'\n')
print(json.dumps({'output':str(out),'files':sum(f.is_file()for f in out.rglob('*'))}))
