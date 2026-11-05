"""Read-only frozen MIR control-flow certificates; no inferred SDK alias facts."""
from pathlib import Path
import re,json,lzma,hashlib,sys
E=Path(__file__).resolve().parent
P=E.parent/'pool-borrow-20261107/NIK_M001_artifacts/NIK_pool.mir.xz'
raw=lzma.decompress(P.read_bytes());assert hashlib.sha256(raw).hexdigest()=='1f27192d86b2642c7da0d4dbade3ab89b43da28357e972fac7f7247949a6d330'
s=raw.decode();functions={}
for m in re.finditer(r'^fn ([^\n]+)\{',s,re.M):
 if '::{closure#' in m[1]:continue
 name=m[1].split('(')[0];end=m.end()+re.search(r'^}',s[m.end():],re.M).end();text=s[m.start():end]
 matches=list(re.finditer(r'^    bb([0-9]+)(?: \(cleanup\))?: \{',text,re.M));blocks={}
 for i,b in enumerate(matches):
  body=text[b.end():matches[i+1].start() if i+1<len(matches) else len(text)]
  blocks[int(b[1])]=dict(successors=sorted(set(int(z) for z in re.findall(r'\bbb([0-9]+)\b',body))),body=body)
 assert len(blocks)==len(matches)
 assert all(t in blocks for b in blocks.values() for t in b['successors'])
 functions[name]=dict(header=m.group(),text_sha256=hashlib.sha256(text.encode()).hexdigest(),blocks=blocks)

specs=[('forest_deposit','process_pair_forest_deposit_with_runtime_v1','require_unique_accounts('),('forest_terminal','process_pair_forest_terminal_with_verifier_v1','plan_pair_forest_spend_layout_v1('),('pair_withdrawal','process_pair_withdrawal_with_verifier_v1','require_unique(')]
out=[]
for label,name,pattern in specs:
 f=functions[name];bbs=f['blocks'];barriers=[n for n,b in bbs.items() if pattern in b['body']];assert len(barriers)==1,(name,barriers)
 barrier=barriers[0];targets=[n for n,b in bbs.items() if '= const -1_isize;' in b['body']];assert targets
 seen={0};todo=[0]
 while todo:
  n=todo.pop()
  if n==barrier:continue
  for target in bbs[n]['successors']:
   if target not in seen:seen.add(target);todo.append(target)
 hits=sorted(set(targets)&seen)
 edges=[dict(source=n,target=t,safe_source=n in seen,safe_target=t in seen,barrier_source=n==barrier) for n,b in bbs.items() for t in b['successors']]
 out.append(dict(label=label,function=name,header=f['header'],mir_function_sha256=f['text_sha256'],barrier=barrier,barrier_pattern=pattern,targets=targets,targets_classification='Candidate inlined exclusive-counter stores; SAME data-cell/source-guard association is a separate obligation.',reachable_without_barrier=sorted(seen),intersections=hits,edges=edges,blocks=len(bbs),status='CFG_DOMINANCE_CANDIDATE' if not hits else 'CFG_INTERSECTION_FINDING'))
(E/'NIZ_CFG_CERTIFICATES.json').write_text(json.dumps(dict(mir_path=str(P),mir_sha256=hashlib.sha256(raw).hexdigest(),method='All normal/error/unwind MIR successors; syntactic -1 counter stores remain candidates, not a source ownership proof.',certificates=out),indent=2))
print(json.dumps([dict(site=x['label'],blocks=x['blocks'],edges=len(x['edges']),barrier=x['barrier'],targets=x['targets'],intersections=x['intersections']) for x in out]))
