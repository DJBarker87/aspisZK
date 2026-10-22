#!/usr/bin/env python3
"""Extract full CFGs behind all 140 retained dominance observations."""
import hashlib,json,re
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-repin-20261022')
P=H
x=json.loads((P/'packet/ordering-observations.json').read_text());rows=[]
for r in x['functions']:
    if not r['dominance']:continue
    p=Path(r['path']);lines=p.read_text().splitlines();start=r['line']-1;end=start+1
    while lines[end]!='}':end+=1
    body='\n'.join(lines[start:end+1])+'\n'
    assert hashlib.sha256(body.encode()).hexdigest()==r['body_sha256']
    blocks={};current=None
    for l in lines[start:end+1]:
        m=re.match(r'    bb(\d+)(?: \(cleanup\))?: \{',l)
        if m:current=int(m[1]);blocks[current]=[]
        elif current is not None:blocks[current].append(l)
    edges=sorted((a,int(b)) for a,ls in blocks.items() for b in set(re.findall(r'\bbb(\d+)\b','\n'.join(ls))))
    assert len(blocks)==r['blocks']
    cuts=[]
    for f in r['dominance']:
        cut=int(f['before_block'][2:]);target=int(f['after_block'][2:])
        reachable=set() if cut==0 else {0};todo=list(reachable)
        while todo:
            a=todo.pop()
            for src,dst in edges:
                if src==a and dst!=cut and dst not in reachable:reachable.add(dst);todo.append(dst)
        assert target not in reachable
        assert all(dst==cut or src not in reachable or dst in reachable for src,dst in edges)
        cuts.append(dict(**f,cut=cut,target=target,reachable_without_cut=sorted(reachable)))
    rows.append(dict(mode=r['mode'],path=r['path'],line=r['line'],header=r['header'],body_sha256=r['body_sha256'],blocks=len(blocks),edges=edges,cuts=cuts))
assert sum(len(r['cuts']) for r in rows)==140
result=dict(schema='s10-pass4-cfg-cut-certificates-v1',functions=rows,generator='tools/s10-inventory4-20261021/cfg-host.py',
    scope='Exact pinned frozen MIR graph. Paths are graph paths; no semantic execution/caller substitution is asserted.')
p=H/'cfg.json';p.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size,functions=len(rows),cuts=140)),flush=True)
