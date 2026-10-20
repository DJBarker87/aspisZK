#!/usr/bin/env python3
"""Read-only retrieval of the missing, source-indexed retained sampler closure."""
from pathlib import Path
import json,re,subprocess,hashlib
repo=Path(__file__).resolve().parents[2]
here=repo/'docs/research/100bit-spend-path-20261013/evidence/r4-transport-20261021'
roots=[repo/'docs/research/v8-full-view-zk-20260912/lean',repo/'docs/research/100bit-spend-path-20261013/lean',repo/'AspisFormal']
overlay=Path('/tmp/codex-cx-r4-transport-20261021-imports')
output=Path('/tmp/codex-cx-r4-transport-upstream-objects')
queue=['AspisV8R19.SamplerClosureCircleSourceExecution','AspisV8R19.SamplerClosureProductCorrectness','AspisV8R19.SamplerClosureCircleScalarTransport']
seen=set();missing=[];sources=[]
while queue:
 name=queue.pop()
 if name in seen:continue
 seen.add(name);rel=Path(name.replace('.','/')).with_suffix('.lean')
 src=next((r/rel for r in roots if (r/rel).is_file()),None)
 obj=overlay/name.replace('.','/');obj=obj.with_suffix('.olean')
 if not obj.is_file() and (name.startswith('Aspis') or name.startswith('R0')):missing.append(name)
 if src:
  sources.append({'module':name,'path':str(src.relative_to(repo)),'sha256':hashlib.sha256(src.read_bytes()).hexdigest()})
  queue.extend(re.findall(r'^import\s+(\S+)',src.read_text(),re.M))
plan={'missing':sorted(missing),'source_closure':sources}
(here/'missing-sampler-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
print('Missing selected objects',len(missing),flush=True)
# Read-only remote metadata first; no transfer unless total is below64MiB.
remote='dombarker@100.108.41.90'
script='''import json,hashlib\nfrom pathlib import Path\nroots=[Path('/tmp/r1-circle-fallback-coalesced-native-closure-v8/objects'),Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/objects')]\nrows=[]\nfor name in NAMES:\n rel=Path(name.replace('.','/')).with_suffix('.olean')\n p=next((r/rel for r in roots if (r/rel).is_file()),None)\n rows.append({'module':name,'path':str(p) if p else None,'sha256':hashlib.sha256(p.read_bytes()).hexdigest() if p else None,'bytes':p.stat().st_size if p else None})\nprint(json.dumps(rows))\n'''.replace('NAMES',repr(sorted(missing)))
rows=json.loads(subprocess.check_output(['ssh',remote,'python3 -'],input=script,text=True))
assert sum(r['bytes'] or 0 for r in rows)<64*2**20
by_namespace={}
for r in rows:
 if r['path']:
  group=r['module'].rsplit('.',1)[0];by_namespace.setdefault(group,[]).append(r)
for group,rs in by_namespace.items():
 dest=output/group.replace('.','/');dest.mkdir(parents=True,exist_ok=True)
 subprocess.run(['scp',*[remote+':'+r['path'] for r in rs],str(dest)+'/'],check=True)
 for r in rs:
  f=output/Path(r['module'].replace('.','/')).with_suffix('.olean')
  assert hashlib.sha256(f.read_bytes()).hexdigest()==r['sha256']
(here/'fetched-missing-sampler-objects.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Fetched bytes',sum(r['bytes'] or 0 for r in rows),flush=True)
