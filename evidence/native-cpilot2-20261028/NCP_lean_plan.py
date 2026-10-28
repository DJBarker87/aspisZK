from pathlib import Path
import NCP_runner as m
import json,subprocess,re
C='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025';cache='/home/dombarker/project-offloads/codex-cx-cpilot2-cache-20261028'
r=m.py(f'''from pathlib import Path
import json
roots=[{cache!r},{C!r},{(C+'/objects')!r},'/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean']
print(json.dumps(sorted(set(str(p.relative_to(root))[:-6].replace('/','.') for root in roots for p in Path(root).rglob('*.olean')))))
''');assert r.returncode==0,r.stderr
have=set(json.loads(r.stdout));jobs=[];seen=set()
def visit(name):
 if name in have or name in seen:return
 seen.add(name)
 p=Path('lean')/(name.replace('.','/')+'.lean')
 if not p.is_file():raise SystemExit('Missing source for private dependency: '+name)
 for line in p.read_text().splitlines():
  if line.startswith('import '):
   for dep in line[7:].split():visit(dep)
 jobs.append({'module':name,'source':str(p)})
visit('NCP_ModelDischarge')
(m.E/'NCP_LEAN_PLAN.json').write_text(json.dumps(jobs,indent=2))
print(len(jobs),json.dumps(jobs))
