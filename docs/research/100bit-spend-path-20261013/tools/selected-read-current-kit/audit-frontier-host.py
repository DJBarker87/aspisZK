#!/usr/bin/env python3
"""Read-only historical/current selected-read reverse-closure audit. No compiler."""
from pathlib import Path
import json,re,hashlib,importlib.util
P=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-typedfull-current-20261017');O=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/bridge');sp=importlib.util.spec_from_file_location('r',P/'runner.py');r=importlib.util.module_from_spec(sp);sp.loader.exec_module(r);D=json.loads((P/'external-inputs.json').read_text());pm=json.loads((P/'sources/SOURCE-MANIFEST.json').read_text())
current={n:v for n,v in D['modules'].items()}
for n,v in pm['modules'].items():
 rc=json.loads((P/'successful-targets'/(n+'.json')).read_text());current[n]={'source':str(P/'sources'/(r.stem(n)+'.lean')),'source_sha256':v['source_sha256'],'objects':rc['objects'],'imports':r.imports(P/'sources'/(r.stem(n)+'.lean'),True)}
oldmanifest=json.loads((O/'input-manifest-v2.json').read_text());G={};missing=[]
# Resolve exact old project snapshots, then current pinned runtime/backend/package
# sources. Standard-library leaves need no historic project refresh.
def resolve(n):
 p=O/'sources'/(r.stem(n)+'.lean')
 if p.exists():return p
 if n in current:return Path(current[n]['source'])
 for root in D['roots']:
  p=Path(root['source'])/(r.stem(n)+'.lean')
  if p.exists():return p
 return None
def visit(n):
 if n in G:return
 p=resolve(n)
 if p is None:missing.append(n);G[n]={'imports':[],'missing':True};return
 ds=r.imports(p,True);G[n]={'source':str(p),'source_sha256':r.sha(p),'imports':ds}
 for dep in ds:visit(dep)
for n in ['R1SemanticPrefixCompletedAgreement','R1SemanticPrefixCutAgreement']:visit(n)
seeds={'FS2.Duplex','AspisV8R19.UniformStateFirstHit','AspisFormal.CircleGroupOrder'};affected=seeds&set(G)
while True:
 more={n for n,v in G.items() if set(v['imports'])&affected}-affected
 if not more:break
 affected|=more
sourcechanges=[];objectconflicts=[];off=[];need=[]
for n,v in G.items():
 if v.get('missing'):continue
 op=O/'objects'/(r.stem(n)+'.olean');oh=r.sha(op) if op.exists() else None;v['historical_object']=str(op) if op.exists() else None;v['historical_object_sha256']=oh
 if n in current:
  c=current[n];v['current_source']=c['source'];v['current_source_sha256']=c['source_sha256'];v['current_object']=c['objects']['.olean']['path'];v['current_object_sha256']=c['objects']['.olean']['sha256']
  if v['source_sha256']!=c['source_sha256']:sourcechanges.append(n)
  if oh and oh!=c['objects']['.olean']['sha256']:objectconflicts.append(n)
 if n in affected:need.append(n)
 elif n not in current:off.append(n)
# Topological projected refresh order. Current already-refreshed sources/objects
# are not rebuilt, but ANY historical dependent of a changed seed is excluded.
order=[];seen=set()
def topo(n):
 if n in seen:return
 for dep in G[n]['imports']:topo(dep)
 seen.add(n)
 if n in affected and n not in current:order.append(n)
for n in ['R1SemanticPrefixCompletedAgreement','R1SemanticPrefixCutAgreement']:topo(n)
result={'read_only':True,'targets':['R1SemanticPrefixCompletedAgreement','R1SemanticPrefixCutAgreement'],'historical_manifest_sha256':r.sha(O/'input-manifest-v2.json'),'current_external_snapshot_sha256':r.sha(P/'external-inputs.json'),'graph_modules':len(G),'unresolved':missing,'changed_source_modules':sourcechanges,'conflicting_historical_objects':objectconflicts,'three_seed_reverse_closure':sorted(affected),'fresh_affected_not_current_topological':order,'off_reverse_closure_not_current':off,'modules':G,'release_rule':'No historical object is accepted here. Reuse outside reverse cone still needs exact producing source/object/import identity. Refresh only missing reverse cone against current seed objects; changed-source declarations need statement diffs. No compiler executed.'};r.dump(P/'selected-read-reverse-frontier.json',result);print(json.dumps({k:v for k,v in result.items() if k!='modules'},indent=2))
