from pathlib import Path
import json,hashlib,importlib.util,collections
B=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/bridge')
S=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/extracted/j1-r17-build-extracted-v2.py')
sp=importlib.util.spec_from_file_location('r',S);r=importlib.util.module_from_spec(sp);sp.loader.exec_module(r)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((B/'manifest.json').read_text());pins=m['dependency_pins'];g={};meta={}
for n,v in (pins|m['new_targets']).items():
 p=B/v['source_snapshot'];s=p.read_text();g[n]=r.imports(p,implicit_init=True)
 meta[n]={'source_sha256':sha(p),'bytes':p.stat().st_size,'lines':len(s.splitlines()),'source_snapshot':str(p),'imports':g[n],
 'mentions_generator_or_certificate':any(w in s.lower() for w in ['auto-generated','automatically generated','generated certificate','generated-certificate','certificate chunk']),
 'proof_shape_review_flags':[w for w in ['maxRecDepth','maxHeartbeats','native_decide','norm_num','decide'] if w in s],
 'object_sha256':pins.get(n,{}).get('object_sha256')}
def path_to(start,target):
 q=collections.deque([(start,[start])]);seen=set()
 while q:
  n,p=q.popleft()
  if n==target:return p
  if n in seen:continue
  seen.add(n)
  for d in g.get(n,[]):q.append((d,p+[d]))
 return None
bad='AspisFormal.CircleGroupOrder';affected={n:v for n,v in meta.items() if n!=bad and path_to(n,bad)}
receipts=[]
for run in ['primitive-linux-d','completed-linux-a','cut-linux-a']:
 d=B/'runs'/run;p=d/'receipt.json';v=json.loads(p.read_text());n=v['target'];src=d/'source.lean';assert sha(src)==v['source_sha256']
 ds=r.imports(src,implicit_init=True);direct={}
 for x in ds:
  if x=='Init':continue
  if x in pins:
   obj=B/pins[x]['object_snapshot'];expected=pins[x]['object_sha256']
  else:
   obj=B/'objects'/(x.replace('.','/')+'.olean');expected=None
   for z in ['primitive-linux-d','completed-linux-a','cut-linux-a']:
    rr=json.loads((B/'runs'/z/'receipt.json').read_text())
    if rr['target']==x:expected=rr['olean_sha256']
  assert expected and sha(obj)==expected,(n,x)
  direct[x]={'object_sha256':expected,'object_path':str(obj),'source_path_to_rejected_circle':path_to(x,bad)}
 receipts.append({'run':run,'receipt_sha256':sha(p),'source_snapshot_sha256':sha(src),'receipt':v,'actual_direct_imports_from_receipt_pinned_source':direct})
result={'scope':'Size/shape inventory and actual three receipt-pinned sources/direct objects; transitive paths are source graph only, not newly audited historical object headers.',
 'affected_source_graph':affected,'size_bands':{label:sum(lo<=v['bytes']<hi for v in affected.values()) for label,lo,hi in [('under16KiB',0,16384),('16to64KiB',16384,65536),('64to256KiB',65536,262144),('atleast256KiB',262144,10**20)]},
 'total_source_bytes':sum(v['bytes'] for v in affected.values()),'largest20':sorted(affected,key=lambda n:affected[n]['bytes'],reverse=True)[:20],
 'generated_marker_modules':[n for n,v in affected.items() if v['mentions_generator_or_certificate']],
 'actual_target_receipts':receipts,'historical_circle_source_receipt':'OPEN; no matching producing receipt established by this inventory.'}
print(json.dumps(result,indent=2,sort_keys=True))
