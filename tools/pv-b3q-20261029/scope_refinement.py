"""Remove only mechanically impossible lexical-scope edges; retain all other
conservative edges. This is not a complete deployed call-graph certificate."""
from pathlib import Path
import json,hashlib,re
B=Path('evidence/pv-b3p6-20261028');D=Path('evidence/pv-b3q-20261029');x=json.loads((B/'resume11/reachability.json').read_text());inv=json.loads((B/'resume9/body-inventory.json').read_text());s=Path('tools/pv-b3p6-20261028/v244/host_terminal.rs').read_text()
rows=x['bodies'];nodes={}
for r in rows:
 n=r['source_node']
 if n and not n['disabled']and not n['template']:nodes['source:'+r['family']+':'+r['key']]=n
byname={}
for k,n in nodes.items():byname.setdefault(n['name'],[]).append(k)
public=next(r for r in inv['bodies']if r['family']=='terminal'and r['key']=='public_bytes#0')['source'];a=sum(len(l)for l in s.splitlines(keepends=True)[:public['line']-1]);b=sum(len(l)for l in s.splitlines(keepends=True)[:public['end_line']]);outer=s[a:b]
assert 'fn fields('in outer and 'fn frontier('in outer
assert re.search(r'fn validate_transition\([\s\S]+?source\.frontier',s)
# Both functions are nested items, inaccessible to callers outside this method.
allowed={'source:terminal:public_bytes#0','source:terminal:frontier#0'}
root='source:terminal:terminal_qm31#0';seen={root};queue=[root];removed=[]
while queue:
 k=queue.pop(0)
 for name in nodes[k]['identifiers']:
  for target in byname.get(name,[]):
   if target in ['source:terminal:frontier#0','source:terminal:fields#0']and k not in allowed:
    removed.append(dict(caller=k,target=target,reason='callee is nested inside Public::public_bytes and is not in caller lexical scope; frontier here is a [Digest;20] field'))
    continue
   if target not in seen:seen.add(target);queue.append(target)
previous={k for k in nodes if any(r['source_path']and r['source_path'][-1]==k for r in rows)}
removed_nodes=sorted(previous-seen)
assert removed_nodes==['source:terminal:fields#0','source:terminal:frontier#0'],removed_nodes
llvm=json.loads((B/'resume7/llvm227-trace-resume7.json').read_text());assert not llvm['indirect_calls']
assert all(not any(word in(r['description']or'')for word in ['public_bytes','alloc::vec','__rust_alloc','frontier'])for r in llvm['reachable_functions'])
x=dict(previous_conservative_candidates=len(previous),refined_conservative_candidates=len(seen),removed_edges=removed,removed_nodes=removed_nodes,source_sha256=hashlib.sha256(s.encode()).hexdigest(),public_bytes_span=public,exact_deployed_cone_certified=False,scope_rule='Rust nested function item lexical scope; non-call field references do not name inaccessible function items',supporting_llvm='resume7/llvm227-trace-resume7.json: no indirect calls or Vec/allocator/public_bytes symbol in inspected cone; optimized absence alone is not the proof',remaining='complete external pre-inline closure and dispatch reconciliation',existing_PV_B3P_links_changed=False,root_fields_link_status='unchanged/open; lexical unreachability does not prove a universal fields port equality')
(D/'scope-refinement.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:x[k]for k in ['previous_conservative_candidates','refined_conservative_candidates','removed_nodes','exact_deployed_cone_certified']}))
