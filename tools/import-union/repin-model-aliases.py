#!/usr/bin/env python3
"""Pin one owner for historical model aliases; replay the actual reverse closure.

Never edits historical/candidate sources or shared objects. SpendRelation keeps
its current AppendBinding contract; source selection cannot erase that premise.
"""
import argparse, hashlib, json, re, shutil, subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
BASE=ROOT/'docs/research/100bit-spend-path-20261013'
ap=argparse.ArgumentParser()
ap.add_argument('plan',type=Path);ap.add_argument('graph',type=Path);ap.add_argument('staging',type=Path)
a=ap.parse_args();plan=json.loads(a.plan.read_text());providers=json.loads(a.graph.read_text())
existing={r['module']:r for r in plan['ordered'] if r['module'] not in ['ProviderGraphPreflight','RawCollisionPreflight']}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def imports(p):
 return [m for l in re.findall(r'^\s*import\s+([^\n]+)',p.read_text(),re.M) for m in l.split('--')[0].split()]
canonical={m:BASE/'lean'/(m+'.lean') for m in ['R1D18Transport','R1PoseidonMap','R1SpendRelation','D18Transport','PoseidonMap','SpendRelation']}
canonical['RawUnionScan']=ROOT/'tools/import-union/RawUnionScan.lean'
# Current canonical protocol includes its documented specification-level default
# extractor. The j1-r7-r8 archive predates that backward-compatible default.
canonical['R1LiteralByteProtocol']=BASE/'lean/LiteralByteProtocol.lean'
# This retained source already proves AppendBinding; older extraction archives
# target the weaker legacy relation and are not eligible providers.
canonical['R1SpendRelationExtraction']=BASE/'evidence/lean-j1-r2-requested-check-20261015/sources/R1SpendRelationExtraction.lean'
tracked=[ROOT/p for p in subprocess.check_output(['git','ls-files','*.lean'],text=True,cwd=ROOT).splitlines() if p.startswith('docs/research/')]
def source(m):
 if m in canonical:return canonical[m]
 if m in existing:return ROOT/existing[m]['path']
 ps=[p for p in tracked if p.as_posix().endswith('/'+m.replace('.','/')+'.lean')]
 if not ps and m.startswith('R1'):
  ps=[p for p in tracked if p.as_posix().endswith('/'+m[2:].replace('.','/')+'.lean')]
 if not ps:raise RuntimeError('Missing source '+m)
 return min(ps,key=lambda p:(0 if str(p).startswith(str(BASE/'lean')+'/') else 1 if '/lean/' in str(p) and '/evidence/' not in str(p) else 2 if '/lean-candidates/' in str(p) else 3,str(p)))
graph={m:r['imports'] for m,r in providers.items()};graph.update({m:r['imports'] for m,r in existing.items()})
for m,p in canonical.items():graph[m]=imports(p)
affected={'R1D18Transport','R1PoseidonMap','R1SpendRelation'}
while True:
 new=affected|{m for m in graph if any(d in affected for d in graph[m])}
 if new==affected:break
 affected=new
# Pin source dependencies introduced by these exact current providers as well.
required=affected|set(canonical)
while True:
 before=set(required)
 for m in list(required):
  p=source(m);graph[m]=imports(p)
  for d in graph[m]:
   if d not in providers and d not in existing and d.split('.')[0] not in ['Init','Lean','Std','Mathlib','Batteries','Aeneas','AeneasMeta','Aesop','Qq','Plausible','ProofWidgets','ImportGraph','LeanSearchClient','Lake']:required.add(d)
 if required==before:break
stamp='canonical-model-aliases-append-binding-v1'
for m in required:
 p=source(m)
 existing[m]={'module':m,'path':str(p.relative_to(ROOT)),'sha256':sha(p),'imports':imports(p),'affected':True,'rebuild_epoch':stamp}
# Include the aggregate and metadata root in dependency order.
ordered=[];done=set();active=set()
def visit(m):
 if m in done:return
 if m in active:raise RuntimeError('cycle '+m)
 active.add(m)
 for d in existing[m]['imports']:
  if d in existing:visit(d)
 active.remove(m);done.add(m);ordered.append(existing[m])
for r in plan['ordered']:
 if r['module'] in existing:visit(r['module'])
for m in sorted(required):visit(m)
plan['ordered']=ordered;plan['changed_modules']=sorted(set(plan['changed_modules'])|set(canonical)-{'RawUnionScan','R1SpendRelationExtraction'})
plan['revision']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
a.staging.mkdir(parents=True,exist_ok=True)
for m in required:
 p=source(m);dest=a.staging/'sources'/(m.replace('.','/')+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest)
(a.staging/'plan.json').write_text(json.dumps(plan,indent=2,sort_keys=True)+'\n')
(a.staging/'model-alias-repin.json').write_text(json.dumps({'roots':['R1D18Transport','R1PoseidonMap','R1SpendRelation'],'affected':sorted(affected),'required':sorted(required),'sources':{m:existing[m] for m in sorted(required)},'epoch':stamp,'shared_objects_overwritten':False,'spend_contract':'Canonical SpendRelation includes AppendBinding; legacy cached R1SpendRelation omits it.'},indent=2,sort_keys=True)+'\n')
print('affected',len(affected),'staged',len(required),'total',len(ordered))
