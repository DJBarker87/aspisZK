#!/usr/bin/env python3
"""Public source/measurement evidence only; never collect keys or proof secrets."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
out=a.output;assert not out.exists();out.mkdir(parents=True)
base=Path('/home/dombarker/project-offloads');control=base/'aspis-r20-r69-explicit-20260929-b'
variants=['square','shortdot','semantic','powerbasis','shortinline','compose','privatebasis','scalarg']
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def copy(src,dst):
    assert src.is_file() and 'keypair' not in str(src)
    dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
def blob(src):
    digest=sha(src);dst=out/'blobs'/digest
    if not dst.exists():copy(src,dst)
    else:assert sha(dst)==digest
    return digest
pm=json.loads((control/'r18-stage.json').read_text());assert len(pm['files'])==202
assert sha(control/'r18-stage.json')=='6a8d46585bcebaeca27fbb88c936e2379ce45f3f314a01f7d37d7b995bb8e8ab'
for n,h in pm['files'].items():assert sha(control/n)==h,n
copy(control/'r18-stage.json',out/'control/r18-stage.json')
copy(control/'r24-svm-a/receipt.json',out/'control/svm.json')
control_sources={};collections={}
for variant in variants:
    stage=base/f'aspis-r20-r81-{variant}-20260929-a';d=out/variant
    m=json.loads((stage/'r18-stage.json').read_text());sources={}
    for n,h in m['files'].items():
        assert sha(stage/n)==h,n
        if pm['files'].get(n)!=h:
            sources[n]=blob(stage/n)
            if n in pm['files']:control_sources[n]=blob(control/n)
    copy(stage/'r18-stage.json',d/'r18-stage.json')
    (d/'sources.json').write_text(json.dumps(sources,indent=2)+'\n')
    artifacts={}
    for mode in ['host','sbf','svm']:
        folder=stage/f'r24-{mode}-a'
        for f in sorted(folder.iterdir()):
            if f.is_file() and f.suffix in ['.log','.json']:
                artifacts[f'r24-{mode}-a/{f.name}']=blob(f)
        if mode=='host':
            artifacts['wire-controls.json']=blob(folder/'wire-controls/results.json')
    trace=stage/'full-trace'
    if (trace/'analysis.json').exists():
        for n in ['analysis.json','run.log','receipt.json','mul-inventory.json']:
            if (trace/n).exists():artifacts['full-trace/'+n]=blob(trace/n)
    (d/'artifacts.json').write_text(json.dumps(artifacts,indent=2)+'\n')
    svm=json.loads((stage/'r24-svm-a/receipt.json').read_text())
    assert sha(stage/'sbf-primary/aspis_v8_performance_sbf.so')==svm['elf_sha256']
    collections[variant]={'stage':str(stage),'verified_source_pins':len(m['files']),
        'observed_elf_sha256':svm['elf_sha256'],'source_delta_files':len(sources)}
(out/'control/sources.json').write_text(json.dumps(control_sources,indent=2)+'\n')
for n in ['analysis.json','run.log','receipt.json']:
    copy(control/'full-trace'/n,out/'control/full-trace'/n)
(out/'collection.json').write_text(json.dumps({'base_revision':'4b64f97254e18f0338e1ad6229ca8407143aeb2b',
    'variants':collections,'control_source_pins':202,'private_fixtures_collected':False,
    'wallet_keys_collected':False,'ELFs_collected':False,'raw_register_traces_collected':False},indent=2)+'\n')
print(json.dumps({'output':str(out),'files':sum(f.is_file()for f in out.rglob('*'))}))
