#!/usr/bin/env python3
"""Only public source deltas and logs; retain both successful and slower trials."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
out=a.output;assert not out.exists();out.mkdir(parents=True)
base=Path('/home/dombarker/project-offloads');control=base/'aspis-r20-r61-opening-20260929-a'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(s,d):
    assert s.is_file() and 'keypair' not in str(s)
    d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(s,d)
parent=json.loads((control/'r18-stage.json').read_text())
for n,h in parent['files'].items():assert sha(control/n)==h,n
support='docs/research/v8-no-work-100-20260907/experiments/r18_minimal_support.rs'
copy(control/support,out/'control'/support)
for variant,folder in [('pair','aspis-r20-r62-ordinary-20260929-a'),('gather-old','aspis-r20-r62-gather-20260929-a'),('gather-checked','aspis-r20-r62-gather-20260929-b')]:
    src=base/folder;dest=out/variant;m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==197
    for n,h in m['files'].items():
        assert sha(src/n)==h,n
        if parent['files'][n]!=h:
            copy(src/n,dest/'source'/n)
            if not (out/'control'/n).exists():copy(control/n,out/'control'/n)
    copy(src/'r18-stage.json',dest/'r18-stage.json')
    for folder in ['r24-host-a','r24-sbf-a','r24-svm-a']:
        for f in (src/folder).rglob('*'):
            if f.is_file() and f.suffix in ('.log','.json'):copy(f,dest/folder/f.relative_to(src/folder))
    if (src/'full-trace/analysis.json').exists():
        for n in ['receipt.json','analysis.json','run.log']:copy(src/'full-trace'/n,dest/'full-trace'/n)
for n in ['CorrectionGather.log','metadata.json']:copy(base/'aspis-r62-lean-20260929-a'/n,out/'lean'/n)
print(json.dumps({'output':str(out),'files':sum(f.is_file()for f in out.rglob('*'))}))
