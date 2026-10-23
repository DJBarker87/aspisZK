#!/usr/bin/env python3
"""Compare full records and byte streams; retain hashes only after comparison."""
from pathlib import Path
import hashlib,json,sys
A,B,O=map(Path,sys.argv[1:4]);rows=[]
def compare(a,b):
    ha=hashlib.sha256();hb=hashlib.sha256();equal=True;size=0
    with a.open('rb') as x,b.open('rb') as y:
        while True:
            ax=x.read(1024*1024);by=y.read(1024*1024)
            if not ax and not by:break
            equal=equal and ax==by;ha.update(ax);hb.update(by);size+=len(ax)
    return dict(byte_identical=equal,bytes=size,baseline_sha256=ha.hexdigest(),candidate_sha256=hb.hexdigest())
assert sorted(p.name for p in A.iterdir())==sorted(p.name for p in B.iterdir())
for a in sorted(A.iterdir(),key=lambda p:int(p.name)):
    if not a.is_dir():continue
    b=B/a.name;ar=json.loads((a/'result.json').read_text());br=json.loads((b/'result.json').read_text())
    files={}
    for name in ['public.bin','proof.bin','oracle.bin']:
        x,y=a/name,b/name
        if x.exists() or y.exists():files[name]=compare(x,y) if x.exists() and y.exists() else dict(byte_identical=False)
    rows.append(dict(case=int(a.name),mode=ar['mode'],status=ar['status'],records_equal=ar==br,files=files))
ok=all(r['records_equal'] and all(f['byte_identical'] for f in r['files'].values()) for r in rows)
result=dict(paired_runs=len(rows),passed=ok,fully_executed_proof_pairs=sum(r['status']=='Ok' for r in rows),rejected_prefix_pairs=sum(r['mode']==3 and r['status']=='Ok' for r in rows),oracle_logged_pairs=sum('oracle.bin' in r['files'] for r in rows),coverage={str(i):sum(r['mode']==i for r in rows) for i in range(10)},comparisons=rows)
O.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='comparisons'},indent=2));raise SystemExit(0 if ok else 2)
