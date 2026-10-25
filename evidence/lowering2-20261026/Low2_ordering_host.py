#!/usr/bin/env python3
"""Frozen MIR CFG/dominance observations, not a Program-equality proof.
Textual block order is never interpreted as execution order.
"""
import hashlib,json,re
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-lowering2-20261026')
sha=lambda b:hashlib.sha256(b).hexdigest()
selected={'entrypoint','process_r1_cost_probe_instruction','process','first','first_decoded','tx1','tx2','tx2_authenticated','tx2_common','batch_merkle','batch_merkle_values','query_loop'}
keys=('first','tx1','tx2','parse_shape','canonical_scan','prepare','Accumulator::new','batch_merkle','batch_tree','QueryGeometry','BatchedWeights','checkpoint','resume','finish_relation','query_values','verify_in_place','node_count','process','admitted')
def bodies(p):
 lines=p.read_text().splitlines();i=0
 while i<len(lines):
  if lines[i].startswith('fn '):
   start=i;i+=1
   while i<len(lines) and lines[i]!='}':i+=1
   header=lines[start];name=header.split('(',1)[0][3:].split('::')[-1]
   if name in selected:yield header,start+1,lines[start:i+1]
  i+=1
rows=[]
for mode,build in [('default','build-default-v2'),('devnet','build-devnet-v1'),('pool','build-pool-v1')]:
 for p in sorted((H/build/'compiler-output').glob('*.mir')):
  if p.name.startswith(('aspis_core-','aspis_statement-')):continue
  for header,start,lines in bodies(p):
   blocks={};current=None;calls=[]
   for n,line in enumerate(lines,start):
    m=re.match(r'    (bb\d+)(?: \(cleanup\))?: \{',line)
    if m:current=m[1];blocks[current]=[]
    elif current is not None:
     blocks[current].append(line)
     if ' -> ' in line and '=' in line and not any(t in line for t in ('switchInt(','assert(')):
      calls.append(dict(block=current,line=n,text=line.strip(),selected=any(k in line for k in keys)))
   edges={b:set(re.findall(r'\bbb\d+\b','\n'.join(ls))) for b,ls in blocks.items()}
   assert all(s in blocks for ss in edges.values() for s in ss)
   reachable={'bb0'};todo=['bb0']
   while todo:
    for s in edges[todo.pop()]:
     if s not in reachable:reachable.add(s);todo.append(s)
   parents={b:{a for a in reachable if b in edges[a]} for b in reachable}
   dom={b:({'bb0'} if b=='bb0' else set(reachable)) for b in reachable}
   changed=True
   while changed:
    changed=False
    for b in reachable-{'bb0'}:
     new={b}|set.intersection(*(dom[a] for a in parents[b]))
     if new!=dom[b]:dom[b]=new;changed=True
   chosen=[c for c in calls if c['selected'] and c['block'] in reachable]
   pairs=[dict(before=a['line'],after=b['line'],before_block=a['block'],after_block=b['block']) for a in chosen for b in chosen if a['block']!=b['block'] and a['block'] in dom[b['block']]]
   rows.append(dict(mode=mode,path=str(p),header=header,line=start,body_sha256=sha(('\n'.join(lines)+'\n').encode()),blocks=len(blocks),reachable_blocks=len(reachable),calls=chosen,dominance=pairs,
    scope='Before block dominates after block in this MIR body. Loops/repeated dynamic calls, argument values, acceptance and caller substitution still require semantic proofs.'))
result=dict(schema='s10-frozen-mir-order-observations-v1',functions=rows,inputs=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for build in ('build-default-v2','build-devnet-v1','build-pool-v1') for p in sorted((H/build/'compiler-output').glob('*.mir'))],
 limitation='CFG dominance and ELF byte identity are compiler evidence. They do not construct sourceTree, source_order, model_order, AcceptedRunJoin, account/checkpoint state binding or a probability-law transport.')
raw=(json.dumps(result,indent=2,sort_keys=True)+'\n').encode();assert len(raw)<=5_000_000
(H/'packet/ordering-observations.json').write_bytes(raw)
print(json.dumps(dict(functions=len(rows),selected_calls=sum(len(r['calls']) for r in rows),dominance_pairs=sum(len(r['dominance']) for r in rows),bytes=len(raw))))
