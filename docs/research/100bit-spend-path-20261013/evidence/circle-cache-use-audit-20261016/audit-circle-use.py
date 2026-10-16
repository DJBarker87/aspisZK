#!/usr/bin/env python3
"""Read/hash cached receipts and source import graphs; never compile."""
from pathlib import Path
import importlib.util,json,hashlib
B=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015')
W=B/'extracted'
spec=importlib.util.spec_from_file_location('runner', W/'j1-r17-build-extracted-v2.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
snapshot=read(W/'external-inputs-002.json'); ext=snapshot['modules']
receipts={p.stem:read(p) for p in (W/'successful-targets').glob('*.json')}
graph={n: v['imports'] for n,v in ext.items()}
graph.update({n:list(v['key']['imports']) for n,v in receipts.items()})
def closure(start,g):
 seen=set();pending=list(start);missing=set()
 while pending:
  n=pending.pop()
  if n in seen:continue
  seen.add(n)
  if n not in g:missing.add(n)
  else:pending.extend(g[n])
 return seen,missing
bad_name='AspisFormal.CircleGroupOrder'
bad_sha='39ea3fa6eb53446ecf6cd4a3856219165b247c4175cf79a28313a55958b15597'
rows={}
for n,v in receipts.items():
 c,m=closure([n],graph);assert not m,(n,m)
 rows[n]={'receipt_sha256':sha(W/'successful-targets'/f'{n}.json'),'direct_imports':list(v['key']['imports']),'project_receipt_closure':sorted(c & receipts.keys()),'closure_count':len(c),'Circle_in_closure':bad_name in c,'rejected_hash_in_receipt':bad_sha in json.dumps(v)}
 for im,p in v['key']['imports'].items():
  upstream=receipts.get(im,ext.get(im));assert upstream is not None
  for suffix,obj in p['objects'].items():assert obj['sha256']==upstream['objects'][suffix]['sha256'],(n,im,suffix)
bm=read(B/'bridge/manifest.json');bg={}
for n,v in bm['dependency_pins'].items():bg[n]=r.imports(B/'bridge'/v['source_snapshot'],implicit_init=True)
for n,v in bm['new_targets'].items():bg[n]=r.imports(B/'bridge'/v['source_snapshot'],implicit_init=True)
affected=sorted(n for n in bg if n!=bad_name and bad_name in closure([n],bg)[0])
out={'scope':'Read-only receipt-key and source-header graph audit, not a replay or generalized proof that all historic cache mappings are sound.',
 'header_parser':{'path':str(W/'j1-r17-build-extracted-v2.py'),'sha256':sha(W/'j1-r17-build-extracted-v2.py')},
 'rejected_module':bad_name,'rejected_olean_sha256':bad_sha,
 'R17_external_snapshot':{'path':str(W/'external-inputs-002.json'),'sha256':sha(W/'external-inputs-002.json'),'module_count':len(ext),'contains_Circle':bad_name in ext,'contains_rejected_hash':bad_sha in json.dumps(snapshot)},
 'R17_receipts':rows,'R17_affected_consumers':sorted(n for n,v in rows.items() if v['Circle_in_closure'] or v['rejected_hash_in_receipt']),
 'R17_all_direct_import_object_hashes_match_recorded_upstream':True,
 'separate_semantic_prefix_bridge':{'manifest_sha256':sha(B/'bridge/manifest.json'),'Circle_record':bm['dependency_pins'][bad_name],'source_graph_descendants':affected,'new_targets_affected':sorted(set(affected)&bm['new_targets'].keys()),'status':'source/object correspondence of this separate historical bridge cache requires correction; not part of R17 extracted primary69'}}
print(json.dumps(out,indent=2,sort_keys=True))
