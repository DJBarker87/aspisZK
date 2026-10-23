#!/usr/bin/env python3
"""Close a rebuild plan over the final raw graph, including newly exposed imports."""
import argparse,hashlib,json,re,shutil,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];BASE=ROOT/'docs/research/100bit-spend-path-20261013'
ap=argparse.ArgumentParser();ap.add_argument('plan',type=Path);ap.add_argument('pins',type=Path);ap.add_argument('staging',type=Path);a=ap.parse_args()
plan=json.loads(a.plan.read_text());pins=json.loads(a.pins.read_text());providers={r['module']:r for r in pins};graph={m:r['imports'] for m,r in providers.items()}
existing={r['module']:r for r in plan['ordered'] if not r['module'].startswith('ImportUnionRawDuplicateBatch')}
changed=set(plan['changed_modules'])&providers.keys();affected=set(changed)
while True:
 new=affected|{m for m,ds in graph.items() if any(d in affected for d in ds)}
 if new==affected:break
 affected=new
missing=affected-existing.keys()
assert missing,'No missing consumers: do not repeat an unchanged closure replay'
tracked=[ROOT/p for p in subprocess.check_output(['git','ls-files','*.lean'],cwd=ROOT,text=True).splitlines() if p.startswith('docs/research/')]
def source(m):
 if m in existing:return ROOT/existing[m]['path']
 ps=[p for p in tracked if p.as_posix().endswith('/'+m.replace('.','/')+'.lean')]
 if not ps:raise RuntimeError('Missing source '+m)
 return min(ps,key=lambda p:(0 if str(p).startswith(str(BASE/'lean')+'/') else 1 if '/lean/' in str(p) and '/evidence/' not in str(p) else 2 if '/lean-candidates/' in str(p) else 3,str(p)))
def imports(p):return [m for l in re.findall(r'^\s*import\s+([^\n]+)',p.read_text(),re.M) for m in l.split('--')[0].split()]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
replay=set(missing)
while True:
 new=replay|{m for m,ds in graph.items() if any(d in replay for d in ds)}
 if new==replay:break
 replay=new
epoch='complete-raw-closure-v1:'+hashlib.sha256(json.dumps(sorted(missing)).encode()).hexdigest()
required=set(replay)
while True:
 before=set(required)
 for m in list(required):
  p=source(m);ds=imports(p)
  for d in ds:
   if d not in providers and d not in existing and d.split('.')[0] not in ['Init','Lean','Std','Mathlib','Batteries','Aeneas','AeneasMeta','Aesop','Qq','Plausible','ProofWidgets','ImportGraph','LeanSearchClient','Lake']:required.add(d)
 if required==before:break
for m in required:
 p=source(m);existing[m]={'module':m,'path':str(p.relative_to(ROOT)),'sha256':sha(p),'imports':imports(p),'affected':True,'rebuild_epoch':epoch}
# Enumeration depends on runtime object inputs, not only its Lean import.
existing['RawUnionScan']['rebuild_epoch']=epoch+':metadata-enumeration'
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
# Dynamic enumeration must be after every rebuilt proof provider.
ordered=[r for r in ordered if r['module']!='RawUnionScan']+[existing['RawUnionScan']]
plan['ordered']=ordered;plan['affected_in_selected_union']=sorted(affected);plan['reused']={m:r for m,r in plan['reused'].items() if m not in existing};plan['revision']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
a.staging.mkdir(exist_ok=True,parents=True)
for m in required:
 p=source(m);dest=a.staging/'sources'/(m.replace('.','/')+'.lean');dest.parent.mkdir(exist_ok=True,parents=True);shutil.copyfile(p,dest)
(a.staging/'plan.json').write_text(json.dumps(plan,indent=2,sort_keys=True)+'\n')
(a.staging/'closure-completion.json').write_text(json.dumps({'raw_graph_sha256':sha(a.pins),'missing':sorted(missing),'replay':sorted(replay),'required_sources':{m:existing[m] for m in sorted(required)},'epoch':epoch,'reason':'Canonical provider imports exposed additional retained consumers not present in the initial raw graph; source and contract are preserved.'},indent=2,sort_keys=True)+'\n')
print('missing',len(missing),'dependent replay',len(replay),'required',len(required),'total',len(ordered))
