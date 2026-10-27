from pathlib import Path
import json
D=Path('/home/dombarker/project-offloads/codex-pv-integ2-20261027');B=D.parent
p=json.loads((D/'formal-plan.json').read_text());e=json.loads((B/'r1-privacy-build-integration-20261019/env/J.json').read_text())
roots=[D/'objects']+[Path(x) for x in e['LEAN_PATH'].split(':')]
names=set(p['closure'])|set(p['unresolved'])
for v in p['closure'].values():names.update(v['imports'])
missing=[]
for n in names:
 rel=Path(n.replace('.','/')+'.olean')
 if not any((r/rel).is_file() for r in roots):missing.append(n)
(D/'all-missing-objects.json').write_text(json.dumps(sorted(missing),indent=2)+'\n');print(sorted(missing))
