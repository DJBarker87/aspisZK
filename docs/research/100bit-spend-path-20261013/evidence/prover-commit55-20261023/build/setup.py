from pathlib import Path
import json,hashlib
R=Path('/home/dombarker/project-offloads/codex-cx-prover-commit55-20261023'); P=R.with_name('codex-cx-prover-commit54-20261023')
env=json.loads((P/'build/J.json').read_text()); paths=[P/'objects']+[Path(x) for x in env['LEAN_PATH'].split(':')]
(R/'objects').mkdir(exist_ok=True);(R/'sources').mkdir(exist_ok=True)
links=[]
for root in paths:
 if not root.exists(): continue
 for p in root.rglob('*.olean'):
  target=R/'objects'/p.relative_to(root)
  if target.exists():continue
  target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(p.resolve());links.append((str(target),str(p.resolve())))
env['LEAN_PATH']=str(R/'objects')+':'+str(P/'objects')+':'+env['LEAN_PATH']
(R/'build/J.json').write_text(json.dumps(env,indent=2)+'\n')
(R/'build/cache-links.json').write_text(json.dumps(links,indent=2)+'\n')
for dest in (R/'objects').rglob('*.olean'):
 p=dest.resolve()
 for companion,target in [(Path(str(p)+s),Path(str(dest)+s)) for s in ['.private','.server']]+[(p.with_suffix('.ir'),dest.with_suffix('.ir'))]:
  if companion.is_file() and not target.exists():target.symlink_to(companion)
print('Read-only retained cache links:',len(links))
