#!/usr/bin/env python3
"""Replace the stale serializer Types provider and rebuild its retained consumers.

Inputs are the current pinned plan and a raw object-header graph. Historical
sources and shared objects remain read-only. Existing canonical Types already
names its instances; no additional source migration is necessary.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
ROOT=Path(__file__).resolve().parents[2]
BASE=ROOT/'docs/research/100bit-spend-path-20261013'
ap=argparse.ArgumentParser()
ap.add_argument('plan',type=Path)
ap.add_argument('graph',type=Path)
ap.add_argument('staging',type=Path)
args=ap.parse_args()
plan=json.loads(args.plan.read_text())
providers=json.loads(args.graph.read_text())
existing={r['module']:r for r in plan['ordered'] if r['module']!='ProviderGraphPreflight'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def imports(p):
    return [m for line in re.findall(r'^\s*import\s+([^\n]+)',p.read_text(),re.M) for m in line.split('--')[0].split()]
canonical={
 'AspisR1PublicSerializer.Types':BASE/'lean/bridge-verify-prefix-fe80-20261017/AspisR1PublicSerializer/Types.lean',
 'AspisR1PublicSerializer.Funs':BASE/'evidence/lean-public-serializer-source-20261015/AspisR1PublicSerializer/Funs.lean'}
graph={m:r['imports'] for m,r in providers.items()}
graph.update({m:r['imports'] for m,r in existing.items()})
for m,p in canonical.items():graph[m]=imports(p)
reachable=set()
def reach(m):
    if m in reachable:return
    reachable.add(m)
    for d in graph.get(m,[]):reach(d)
for m in existing:reach(m)
affected={'AspisR1PublicSerializer.Types'}
while True:
    new=affected|{m for m in reachable if any(d in affected for d in graph.get(m,[]))}
    if new==affected:break
    affected=new
tracked=[ROOT/p for p in subprocess.check_output(['git','ls-files','*.lean'],cwd=ROOT,text=True).splitlines() if p.startswith('docs/research/')]
def source(m):
    if m in canonical:return canonical[m]
    if m in existing:return ROOT/existing[m]['path']
    ps=[p for p in tracked if p.as_posix().endswith('/'+m.replace('.','/')+'.lean')]
    if not ps:raise RuntimeError('No source for affected provider '+m)
    return min(ps,key=lambda p:(0 if str(p).startswith(str(BASE/'lean')+'/') else 1 if '/lean/' in str(p) and '/evidence/' not in str(p) else 2 if '/lean-candidates/' in str(p) else 3,str(p)))
for m in affected:
    p=source(m)
    existing[m]={'module':m,'path':str(p.relative_to(ROOT)),'sha256':sha(p),'imports':imports(p),
                 'affected':True,'rebuild_epoch':'canonical-public-serializer-types-v1:'+sha(canonical['AspisR1PublicSerializer.Types'])}
    graph[m]=imports(p)
ordered=[];done=set();visiting=set()
def visit(m):
    if m in done:return
    if m in visiting:raise RuntimeError('cycle '+m)
    visiting.add(m)
    for d in graph.get(m,[]):
        if d in existing:visit(d)
    if m in existing:ordered.append(existing[m])
    visiting.remove(m);done.add(m)
for r in plan['ordered']:
    if r['module']!='ProviderGraphPreflight':visit(r['module'])
for m in sorted(affected):visit(m)
plan['ordered']=ordered
plan['changed_modules']=sorted(set(plan['changed_modules'])|{'AspisR1PublicSerializer.Types'})
plan['environment'].pop('IMPORT_UNION_SCAN_INPUT',None)
args.staging.mkdir(parents=True,exist_ok=True)
for m in affected:
    p=source(m);dest=args.staging/'sources'/(m.replace('.','/')+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest)
(args.staging/'plan.json').write_text(json.dumps(plan,indent=2,sort_keys=True)+'\n')
(args.staging/'provider-repin.json').write_text(json.dumps({
 'root':'AspisR1PublicSerializer.Types','canonical_source':str(canonical['AspisR1PublicSerializer.Types'].relative_to(ROOT)),
 'canonical_source_sha256':sha(canonical['AspisR1PublicSerializer.Types']),
 'old_provider':providers['AspisR1PublicSerializer.Types'],
 'affected':sorted(affected),'affected_count':len(affected),'source_modules':{m:existing[m] for m in sorted(affected)},
 'shared_cache_overwritten':False,'reason':'Canonical source already qualifies instances; selected host cache still defines anonymous instances.'},indent=2,sort_keys=True)+'\n')
print('serializer dependent closure',len(affected),'new total targets',len(ordered))
