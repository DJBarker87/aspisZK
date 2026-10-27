#!/usr/bin/env python3
"""Append the next reviewed proof obligation and check the smallest module."""
import pathlib, subprocess, sys, json
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parent.parent
LEAN=ROOT/'docs/research/v8-r0-zk-20261009/lean'
queue=json.loads((HERE/'proof-queue.json').read_text())
state=HERE/'progress.json'
s=json.loads(state.read_text()) if state.exists() else {'index':0,'next_id':53002}
count=int(sys.argv[1]) if len(sys.argv)>1 else 1
for _ in range(count):
    item=queue[s['index']]; f=LEAN/(item['module']+'.lean')
    if item.get('initial') is not None: f.write_text(item['initial'])
    text=f.read_text(); end='end '+item['namespace']
    assert text.rstrip().endswith(end)
    body=item['body']+'\n'+''.join('#print axioms '+name+'\n' for name in item['theorems'])
    f.write_text(text.rstrip()[:-len(end)]+body+end+'\n')
    a=s['next_id'];s['index']+=1;s['next_id']+=1
    state.write_text(json.dumps(s,indent=2)+'\n')
    p=subprocess.run([sys.executable,str(HERE/'run_attempt.py'),str(a),str(f)],cwd=ROOT)
    if p.returncode:sys.exit(p.returncode)
