#!/usr/bin/env python3
"""Collect only named proof/extraction artifacts; no keys or build trees."""
import argparse, json, shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
root=Path('/home/dombarker/project-offloads');out=a.output
assert not out.exists();out.mkdir(parents=True)
def copy(s,d):
    assert s.is_file() and 'keypair' not in str(s)
    d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(s,d)
final=root/'aspis-r65-final-20260929-a'
for n in ['ComplexFieldSlice','ComplexBaseExecution','ComplexInverseExecution']:
    copy(final/(n+'.log'),out/'lean'/(n+'.log'))
for n in ['metadata.json','dependency-pins.json','resources.json']:
    copy(final/n,out/'lean'/n)
copy(final/'source-audit.json',out/'source-audit.json')
extraction=root/'aspis-r65-extracted-20260929-a'
for n in ['lock','extract','translate']:copy(extraction/(n+'.log'),out/'extraction'/(n+'.log'))
for group,suffix,name in [('base','a','ComplexBaseExecution'),('base','b','ComplexBaseExecution'),('inverse','a','ComplexInverseExecution')]:
    source=root/f'aspis-r65-{group}-20260929-{suffix}'
    copy(source/(name+'.log'),out/'development'/f'{group}-{suffix}.log')
    records=json.loads((source/'metadata.json').read_text())
    record=next(r for r in records if r['target_name']=='AspisV8R19/'+name)
    (out/'development'/f'{group}-{suffix}.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'output':str(out),'files':sum(p.is_file() for p in out.rglob('*'))}))
