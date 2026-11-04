"""Fail-closed additive overlay producer; never edits a historical ledger.

Canonical adjacency is re-derived from NDT's two input inventories with its
canonical() normalization. Reviewed edges require separate compiler evidence.
NFZ_EDGES is intentionally empty when the compiler gate has not been met.
"""
import pathlib,json,lzma,hashlib,subprocess,collections,copy,re
E=pathlib.Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(p):
 q=R/p
 return q.read_bytes() if q.exists() else subprocess.check_output(['git','show','HEAD:'+p],cwd=R)
def canonical(s):return re.sub(r'@\d+$','',s)
def put(n,x):(E/n).write_text(json.dumps(x,indent=1)+'\n')
def pinned(p):return dict(path=p,sha256=sha(read(p)))
def graph_from_inventories():
 functions={};inventories=[]
 for tx,p in [('TX1','evidence/native-inv1-20261027/NBI1_INVENTORY.json'),('TX2','evidence/native-inv2-20261027/NBI2_INVENTORY.json')]:
  inv=json.loads(read(p));assert inv.get('source_revision',inv.get('frozen_revision'))=='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
  inventories.append(pinned(p))
  for f in inv['functions']:functions.setdefault(canonical(f['id']),[]).append(f)
 graph={name:set() for name in functions}
 for name,fs in functions.items():
  for f in fs:
   for call in f.get('callees',f.get('calls',[])):
    graph[name].update(canonical(t) for t in call.get('targets',[]) if canonical(t) in functions)
 return graph,inventories

def apply(base,overlay,edge_bytes):
 assert overlay['edge_list_sha256']==sha(edge_bytes),'edge list digest mismatch'
 edges=json.loads(edge_bytes)
 assert overlay['review_status']=='BLOCKED_MISSING_COMPILER_EVIDENCE' if not edges else overlay['review_status']=='REVIEWED'
 out=copy.deepcopy(base);ix=collections.defaultdict(list)
 for r in out['rows']:ix[r['function']].append(r)
 for edge in edges:
  assert edge['kind'] in ['trait-dispatch','callback']
  assert edge['from'] in ix and edge['to'] in ix,'new nodes require explicit row definitions, never silently omitted'
  evidence=edge['evidence'];raw=read(evidence['path']);assert sha(raw)==evidence['sha256']
  assert evidence['method'] in ['rustc-MIR','rustc-unpretty'],'source discovery cannot admit an edge'
  assert evidence['compiler_gate_passed'] is True
  for r in ix[edge['from']]:
   r['canonical_callees']=sorted(set(r['canonical_callees'])|{edge['to']})
   r.setdefault('NFZ_reviewed_edges',[]).append(edge)
 for before,after in zip(base['rows'],out['rows']):
  assert before['row']==after['row'] and before['composed_status']==after['composed_status']
  assert set(before['canonical_callees'])<=set(after['canonical_callees'])
 return out

def main():
 baseline='evidence/ledger7-20261104/NFX_LEDGER.json.xz';raw=read(baseline);base=json.loads(lzma.decompress(raw));graph,inputs=graph_from_inventories()
 differences=[]
 for r in base['rows']:
  if set(r['canonical_callees'])!=graph[r['function']]:differences.append(dict(row=r['row'],function=r['function'],raw_only=sorted(graph[r['function']]-set(r['canonical_callees'])),ledger_only=sorted(set(r['canonical_callees'])-graph[r['function']])))
 # Disclose the exact inherited difference. NFZ neither introduces these
 # removals nor invents retrospective review credit for them.
 expected={'TX1:058','TX2:039'}
 assert {d['row'] for d in differences}==expected
 assert all(d['function']=='crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes' and not d['ledger_only'] and d['raw_only']==['crates/aspis-core/src/field.rs::M31::to_le_bytes','crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes'] for d in differences)
 put('NFZ_BASELINE_GRAPH_DIFF.json',dict(raw_producer='NDT canonical union of NBI inventories',adopted_baseline=baseline,differences=differences,disposition='Inherited downstream graph delta, preserved verbatim from sha256-pinned NFX; not introduced or newly justified by NFZ'))
 graph=collections.defaultdict(set)
 for r in base['rows']:graph[r['function']].update(r['canonical_callees'])
 edges=[];edge_bytes=(json.dumps(edges,indent=1)+'\n').encode();(E/'NFZ_EDGES.json').write_bytes(edge_bytes)
 overlay=dict(name='NFZ frozen-source reviewed inventory edge overlay',schema_version=1,frozen_revision=base['frozen_revision'],review_status='BLOCKED_MISSING_COMPILER_EVIDENCE',edge_list='evidence/inv-defects-20261104/NFZ_EDGES.json',edge_list_sha256=sha(edge_bytes),baseline=pinned(baseline),inventory_inputs=inputs,producer=pinned('evidence/inv-defects-20261104/NFZ_inventory.py'),canonical_producer=pinned('evidence/native-ledger3-20261029/NDT_validate.py'),slice_tool=pinned('evidence/slice-d-define-20261104/NFQ_build.py'),new_rows=[],excluded_rows=[],no_status_promotion=True,reason='NFZ_B001 passed admission, but own overstrict metadata preflight failed before MIR/HIR/typecheck. One allowed scope used; no compiler evidence exists for admission.')
 put('NFZ_OVERLAY.json',overlay);out=apply(base,overlay,edge_bytes)
 assert out==base
 data=json.dumps(out,indent=1).encode();(E/'NFZ_ADMITTED_LEDGER.json.xz').write_bytes(lzma.compress(data));(E/'NFZ_ADMITTED_LEDGER.json.sha256').write_text(sha(data)+'\n')
 put('NFZ_INVENTORY_GRAPH.json',dict(frozen_revision=base['frozen_revision'],producer='NDT inventory union plus NFZ pinned additive overlay',overlay_sha256=sha((E/'NFZ_OVERLAY.json').read_bytes()),adjacency={f:sorted(v) for f,v in sorted(graph.items())}))
 print(json.dumps(dict(rows=len(out['rows']),functions=len(graph),edges=sum(map(len,graph.values())),admitted_edges=0,status_changes=0)))
if __name__=='__main__':main()
