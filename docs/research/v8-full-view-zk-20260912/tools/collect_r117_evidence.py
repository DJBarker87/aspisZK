#!/usr/bin/env python3
"""Collect public native-engine source deltas and receipts, never private fixtures."""
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
control=base/'aspis-r20-r105-parse-20260930-a';pm=json.loads((control/'r18-stage.json').read_text())
for n,h in pm['files'].items():assert sha(control/n)==h,n
copy(control/'r18-stage.json',out/'control/r18-stage.json');records={};original={}
variants={
 'r106-terminal':'aspis-r20-r106-terminal-20260930-a',
 'r107-semantic':'aspis-r20-r107-semantic-20260930-a',
 'r108-decode':'aspis-r20-r108-decode-20260930-a',
 'r109-geometry':'aspis-r20-r109-geometry-20260930-a',
 'r110-norm':'aspis-r20-r110-norm-20260930-a',
 'r111-decode':'aspis-r20-r111-decode-20260930-a',
 'r112-complex':'aspis-r20-r112-complex-20260930-a',
 'r113-copy-a':'aspis-r20-r113-copy-20260930-a',
 'r113-copy-b':'aspis-r20-r113-copy-20260930-b',
 'r114-tag':'aspis-r20-r114-tag-20260930-a',
 'r115-composed-a':'aspis-r20-r115-composed-20260930-a',
 'r115-composed-b':'aspis-r20-r115-composed-20260930-b',
 'r116-query':'aspis-r20-r116-query-20260930-a',
 'r117-primal':'aspis-r20-r117-primal-20260930-a'}
for name,folder in variants.items():
    stage=base/folder;m=json.loads((stage/'r18-stage.json').read_text());sources={};arts={}
    for n,h in m['files'].items():
        assert sha(stage/n)==h,n
        if pm['files'].get(n)!=h:
            sources[n]=blob(stage/n)
            if n in pm['files']:original[n]=blob(control/n)
    d=out/name;copy(stage/'r18-stage.json',d/'r18-stage.json')
    for sub in ['r24-host-a','r24-sbf-a','r24-svm-a','full-trace','full-trace-cap-b']:
        folder=stage/sub
        if not folder.exists():continue
        for f in sorted(folder.iterdir()):
            if f.is_file()and f.suffix in ['.json','.log']:arts[sub+'/'+f.name]=blob(f)
        if(folder/'wire-controls/results.json').exists():arts['wire-controls.json']=blob(folder/'wire-controls/results.json')
    fixtures=[Path(f['path'])for f in m['r105_native']['fixtures']]
    sizes=[{'sha256':sha(f/'proof-1.bin'),'bytes':(f/'proof-1.bin').stat().st_size}for f in fixtures]
    (d/'fixtures.json').write_text(json.dumps(sizes,indent=2)+'\n')
    (d/'sources.json').write_text(json.dumps(sources,indent=2)+'\n')
    (d/'artifacts.json').write_text(json.dumps(arts,indent=2)+'\n')
    records[name]={'stage':str(stage),'pins':len(m['files'])}
# Cap records come from the process's live cgroup, not stale systemd units.
# The first collector queried already-disposed transient units, obtaining
# defaults. That metadata failure is retained locally and is not used as a cap.
(out/'control/sources.json').write_text(json.dumps(original,indent=2)+'\n')
(out/'collection.json').write_text(json.dumps({'variants':records,'private_fixtures_collected':False,
 'ELFs_collected':False,'wallet_keys_collected':False,'raw_registers_collected':False},indent=2)+'\n')
print(json.dumps({'output':str(out),'files':sum(f.is_file()for f in out.rglob('*'))}))
