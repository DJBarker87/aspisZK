#!/usr/bin/env python3
"""Collect scoped public R86--R90 artifacts, never proof fixtures or keys."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
out=a.output;assert not out.exists();out.mkdir(parents=True);base=Path('/home/dombarker/project-offloads')
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def copy(f,to):
    assert f.is_file() and 'keypair' not in str(f)
    to.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(f,to)
def blob(f):
    h=sha(f);to=out/'blobs'/h
    if not to.exists():copy(f,to)
    assert sha(to)==h;return h
control=base/'aspis-r20-r85-compose-20260929-a'
pm=json.loads((control/'r18-stage.json').read_text());original={};records={}
for n,h in pm['files'].items():assert sha(control/n)==h,n
copy(control/'r18-stage.json',out/'control/r18-stage.json')
variants=[*(f'r86-merkle-{s}'for s in 'abc'),*(f'r87-prepare-{s}'for s in 'abcd'),
    'r88-align-a','r89-packed-a','r90-gamma-a']
for variant in variants:
    kind,suffix=variant.rsplit('-',1);stage=base/f'aspis-r20-{kind}-20260929-{suffix}'
    d=out/variant;d.mkdir();m=json.loads((stage/'r18-stage.json').read_text());sources={}
    for n,h in m['files'].items():
        assert sha(stage/n)==h,n
        if pm['files'].get(n)!=h:
            sources[n]=blob(stage/n)
            if n in pm['files']:original[n]=blob(control/n)
    copy(stage/'r18-stage.json',d/'r18-stage.json')
    (d/'sources.json').write_text(json.dumps(sources,indent=2)+'\n')
    arts={}
    for name in ['r24-host-a','r24-sbf-a','r24-svm-a']:
        folder=stage/name
        if not folder.exists():continue
        for f in sorted(folder.iterdir()):
            if f.is_file()and f.suffix in ['.json','.log']:arts[name+'/'+f.name]=blob(f)
        if (folder/'wire-controls/results.json').exists():arts['wire-controls.json']=blob(folder/'wire-controls/results.json')
    (d/'artifacts.json').write_text(json.dumps(arts,indent=2)+'\n')
    records[variant]={'stage':str(stage),'pins':len(m['files'])}
trace=base/'aspis-r20-r87-prepare-20260929-d/full-trace'
for n in ['analysis.json','receipt.json','mul-inventory.json','run.log']:copy(trace/n,out/'trace'/n)
formal=[*(f'query-leaves-{s}'for s in 'abcde'),*(f'query-model-{s}'for s in 'abcde'),
    'query-source-a','query-final-a']
for n in formal:
    kind,suffix=n.rsplit('-',1);folder=base/f'aspis-r86-{kind}-20260929-{suffix}'
    for f in folder.iterdir():
        if f.is_file()and f.suffix in ['.json','.log']:copy(f,out/'lean'/n/f.name)
deps=json.loads((out/'lean/query-final-a/dependency-pins.json').read_text())
for n,h in deps.items():assert sha(Path(n))==h,n
for suffix in 'ab':
    stage=base/f'aspis-r86-query-extract-20260929-{suffix}';d=out/'extraction'/suffix;d.mkdir(parents=True)
    for f in stage.iterdir():
        if f.is_file()and f.suffix in ['.json','.log','.py']:copy(f,d/f.name)
    generated=json.loads((stage/'generated-pins.json').read_text())
    for n,h in generated.items():assert sha(stage/n)==h,n;blob(stage/n)
    pins=json.loads((stage/'source-pins.json').read_text());sources={}
    for n,h in pins['unchanged_source_files'].items():
        f=stage/'source/src'/n
        if n=='lib.rs':assert sha(f)==pins['extraction_lib_sha256']
        else:assert sha(f)==h
        sources[n]=blob(f)
        if n=='lib.rs':original['crates/aspis-core/src/lib.rs']=blob(control/'crates/aspis-core/src/lib.rs')
    for n in ['build.rs','Cargo.toml','Cargo.lock']:sources[n]=blob(stage/'source'/n)
    (d/'sources.json').write_text(json.dumps(sources,indent=2)+'\n')
    (d/'llbc.json').write_text(json.dumps({'sha256':sha(stage/'R86Query.llbc'),'blob':blob(stage/'R86Query.llbc')},indent=2)+'\n')
(out/'control/sources.json').write_text(json.dumps(original,indent=2)+'\n')
(out/'collection.json').write_text(json.dumps({'variants':records,'formal_dependency_pins_verified':len(deps),
    'wallet_keys_collected':False,'private_fixtures_collected':False,'ELFs_collected':False,
    'raw_registers_collected':False},indent=2)+'\n')
print(json.dumps({'output':str(out),'files':sum(f.is_file()for f in out.rglob('*'))}))
