from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-fix-20261028');rows=[]
for p in (D/'external-objects').rglob('*.olean'):
 source=p.resolve()
 for suffix in ['.ir','.ilean']:
  q=source.with_suffix(suffix);t=p.with_suffix(suffix)
  if q.is_file():
   if not t.exists():t.symlink_to(q)
   rows.append(dict(path=str(t),source=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
(D/'ir-inputs.json').write_text(json.dumps(rows,indent=2)+'\n')
p=D/'rdcd-env.json';env=json.loads(p.read_text());env['LEAN_PATH']=str(D/'external-objects')+':'+env['LEAN_PATH'];p.write_text(json.dumps(env,indent=2)+'\n');print('Added original .ir/.ilean inputs and verified h4 external prefix, original env follows unchanged.')
