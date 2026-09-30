#!/usr/bin/env python3
"""Public source deltas/receipts only; no proof fixtures, ELFs or register data."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
out=a.output;assert not out.exists();out.mkdir(parents=True);base=Path('/home/dombarker/project-offloads')
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def copy(f,to):
    assert f.is_file()and 'keypair'not in str(f);to.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(f,to)
def blob(f):
    h=sha(f);to=out/'blobs'/h
    if not to.exists():copy(f,to)
    assert sha(to)==h;return h
control=base/'aspis-r20-r99-fold-20260930-c';pm=json.loads((control/'r18-stage.json').read_text())
for n,h in pm['files'].items():assert sha(control/n)==h,n
copy(control/'r18-stage.json',out/'control/r18-stage.json');records={};original={}
variants={'r101-auth':'aspis-r101-auth-20260930-a','r102-auth':'aspis-r20-r102-auth-20260930-a',
 'r103-words':'aspis-r20-r103-words-20260930-a','r104-aligned':'aspis-r20-r104-aligned-20260930-a',
 'r104-inactive':'aspis-r20-r104-inactive-20260930-a',
 'r105-parse':'aspis-r20-r105-parse-20260930-a','r105-gather':'aspis-r20-r105-gather-20260930-a'}
for name,folder in variants.items():
    stage=base/folder;manifest='r101-stage.json'if name=='r101-auth'else'r18-stage.json'
    m=json.loads((stage/manifest).read_text());sources={};arts={}
    for n,h in m['files'].items():
        assert sha(stage/n)==h,n
        if pm['files'].get(n)!=h:
            sources[n]=blob(stage/n)
            if n in pm['files']:original[n]=blob(control/n)
    d=out/name;copy(stage/manifest,d/manifest)
    for sub in ['host','sbf','svm','r24-host-a','r24-sbf-a','r24-svm-a','full-trace']:
        folder=stage/sub
        if not folder.exists():continue
        for f in sorted(folder.iterdir()):
            if f.is_file()and f.suffix in ['.json','.log']:arts[sub+'/'+f.name]=blob(f)
        if (folder/'wire-controls/results.json').exists():arts['wire-controls.json']=blob(folder/'wire-controls/results.json')
    # Bound proof-size and frontier claims to the exact measured fixtures,
    # without collecting their private fixture directories or contents.
    if name!='r101-auth':
        fixtures=([Path(f['path'])for f in m['r105_native']['fixtures']]if 'r105_native'in m else
            [Path(f['path'])for f in m['r104_native']['fixtures']]if 'r104_native'in m else
            [stage/f'r24-host-a/fixture-world{w}'for w in range(2)])
        sizes=[{'sha256':sha(f/'proof-1.bin'),'bytes':(f/'proof-1.bin').stat().st_size}for f in fixtures]
        (d/'fixtures.json').write_text(json.dumps(sizes,indent=2)+'\n')
    (d/'sources.json').write_text(json.dumps(sources,indent=2)+'\n')
    (d/'artifacts.json').write_text(json.dumps(arts,indent=2)+'\n')
    records[name]={'stage':str(stage),'manifest':manifest,'pins':len(m['files'])}
(out/'control/sources.json').write_text(json.dumps(original,indent=2)+'\n')
(out/'collection.json').write_text(json.dumps({'variants':records,'private_fixtures_collected':False,
 'ELFs_collected':False,'wallet_keys_collected':False,'raw_registers_collected':False},indent=2)+'\n')
print(json.dumps({'output':str(out),'files':sum(f.is_file()for f in out.rglob('*'))}))
