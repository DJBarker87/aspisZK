#!/usr/bin/env python3
"""Public source/certificate/log collection, excluding witnesses and keys."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
out=a.output;assert not out.exists();out.mkdir(parents=True);base=Path('/home/dombarker/project-offloads')
control=base/'aspis-r20-r82-dotinline-20260929-a'
variants={'one-swap-initial':'bitperm-20260929-a','one-swap-dependency':'bitperm-20260929-b',
    'two-swap-affine':'two-swaps-20260929-a','compact':'compact-20260929-a'}
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def copy(f,to):
    assert f.is_file()and 'keypair'not in str(f);to.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(f,to)
def blob(f):
    h=sha(f);to=out/'blobs'/h
    if not to.exists():copy(f,to)
    assert sha(to)==h;return h
pm=json.loads((control/'r18-stage.json').read_text());assert sha(control/'r18-stage.json')=='f70d74f4e479899b7eda0664a4dfdf4b8e8068d7bf9be836a2cd681397167498'
for n,h in pm['files'].items():assert sha(control/n)==h,n
copy(control/'r18-stage.json',out/'control/r18-stage.json');original={};records={}
for variant,suffix in variants.items():
    stage=base/('aspis-r20-r84-'+suffix);d=out/variant;m=json.loads((stage/'r18-stage.json').read_text());sources={}
    for n,h in m['files'].items():
        assert sha(stage/n)==h,n
        if pm['files'].get(n)!=h:
            sources[n]=blob(stage/n)
            if(control/n).exists():original[n]=blob(control/n)
    copy(stage/'r18-stage.json',d/'r18-stage.json');(d/'sources.json').write_text(json.dumps(sources,indent=2)+'\n')
    arts={}
    for name in ['r84-leaf','r84-prefix-world0','r84-prefix-world1','r24-host-a','r24-sbf-a','r24-svm-a']:
        folder=stage/name
        if not folder.exists():continue
        for f in sorted(folder.iterdir()):
            if f.is_file()and f.suffix in ['.json','.log']:arts[name+'/'+f.name]=blob(f)
        if(folder/'wire-controls/results.json').exists():arts['wire-controls.json']=blob(folder/'wire-controls/results.json')
    (d/'artifacts.json').write_text(json.dumps(arts,indent=2)+'\n')
    records[variant]={'stage':str(stage),'pins':len(m['files'])}
(out/'control/sources.json').write_text(json.dumps(original,indent=2)+'\n')
(out/'collection.json').write_text(json.dumps({'variants':records,'wallet_keys_collected':False,'private_fixtures_collected':False,'ELFs_collected':False},indent=2)+'\n')
print(json.dumps({'output':str(out),'files':sum(f.is_file()for f in out.rglob('*'))}))
