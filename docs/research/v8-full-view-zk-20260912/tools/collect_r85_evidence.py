#!/usr/bin/env python3
"""Collect only public source, receipts and logs; never fixtures, keys or ELFs."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
out=a.output;assert not out.exists();out.mkdir(parents=True);base=Path('/home/dombarker/project-offloads')
control=base/'aspis-r20-r84-compact-20260929-a'
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def copy(f,to):
    assert f.is_file()and 'keypair'not in str(f);to.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(f,to)
def blob(f):
    h=sha(f);to=out/'blobs'/h
    if not to.exists():copy(f,to)
    assert sha(to)==h;return h
pm=json.loads((control/'r18-stage.json').read_text())
for n,h in pm['files'].items():assert sha(control/n)==h,n
copy(control/'r18-stage.json',out/'control/r18-stage.json');original={};records={}
for variant in ['quotient-a','quotient-b','ordinary-a','ordinary-b','compose-a']:
    kind,suffix=variant.rsplit('-',1);stage=base/f'aspis-r20-r85-{kind}-20260929-{suffix}'
    d=out/variant;d.mkdir();m=json.loads((stage/'r18-stage.json').read_text());sources={}
    for n,h in m['files'].items():
        assert sha(stage/n)==h,n
        if pm['files'].get(n)!=h:sources[n]=blob(stage/n);original[n]=blob(control/n)
    copy(stage/'r18-stage.json',d/'r18-stage.json');(d/'sources.json').write_text(json.dumps(sources,indent=2)+'\n')
    arts={}
    for name in ['r24-host-a','r24-sbf-a','r24-svm-a']:
        folder=stage/name
        if not folder.exists():continue
        for f in sorted(folder.iterdir()):
            if f.is_file()and f.suffix in ['.json','.log']:arts[name+'/'+f.name]=blob(f)
        if(folder/'wire-controls/results.json').exists():arts['wire-controls.json']=blob(folder/'wire-controls/results.json')
    (d/'artifacts.json').write_text(json.dumps(arts,indent=2)+'\n');records[variant]={'stage':str(stage),'pins':len(m['files'])}
(out/'control/sources.json').write_text(json.dumps(original,indent=2)+'\n')
for n in ['analysis.json','receipt.json','mul-inventory.json','run.log']:
    copy(control/'full-trace'/n,out/'trace'/n)
formal=['circle-loop-'+s for s in 'abc']+['circle-bridge-a']+['cache-law-'+s for s in 'abc']+['circle-program-'+s for s in 'abc']+['circle-final-a']
for n in formal:
    kind,suffix=n.rsplit('-',1);folder=base/f'aspis-r85-{kind}-20260929-{suffix}'
    for f in folder.iterdir():
        if f.is_file()and f.suffix in ['.json','.log']:copy(f,out/'lean'/n/f.name)
deps=json.loads((out/'lean/circle-final-a/dependency-pins.json').read_text())
for n,h in deps.items():assert sha(Path(n))==h,n
(out/'collection.json').write_text(json.dumps({'variants':records,'formal_dependency_pins_verified':len(deps),
    'wallet_keys_collected':False,'private_fixtures_collected':False,'ELFs_collected':False,'raw_registers_collected':False},indent=2)+'\n')
print(json.dumps({'output':str(out),'files':sum(f.is_file()for f in out.rglob('*'))}))
