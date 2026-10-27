from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-dict2-20261027');env=json.loads((D/'env-J.json').read_text());roots=[D/'lean-objects']+[Path(p) for p in env['LEAN_PATH'].split(':')];mods=json.loads((D/'audit-loaded-modules.json').read_text());rows=[]
for m in mods:
 rel=m.replace('.','/')+'.olean';p=next((d/rel for d in roots if (d/rel).is_file()),None)
 if p:rows.append(dict(module=m,path=str(p),resolved_path=str(p.resolve()),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
 else:rows.append(dict(module=m,missing=True))
(D/'audit-object-bindings.json').write_text(json.dumps(dict(phase='read-only inventory immediately after J54897; no intervening own scope',source_revision=(D/'source-revision.txt').read_text().strip(),environment=env,objects=rows),indent=2)+'\n');print('objects',len(rows),'missing',sum(r.get('missing',False) for r in rows))
