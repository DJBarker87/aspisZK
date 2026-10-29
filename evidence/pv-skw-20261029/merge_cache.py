from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-skw-20261029')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((D/'reuse.json').read_text());rows={};conflicts=[]
for tag in ['diag','l1']:
 for m,v in r[tag]['rows'].items():
  if v.get('external'):continue
  if m in rows:assert rows[m]['sha256']==v['sha256'],m
  p=D/'objects'/(m.replace('.','/')+'.olean')
  if p.exists() and sha(p)!=v['sha256']:conflicts.append(m)
  rows[m]=v
assert not conflicts,conflicts
for m,v in rows.items():
 p=Path(v['object']);assert sha(p)==v['sha256'],m
 q=D/'objects'/(m.replace('.','/')+'.olean');q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():q.symlink_to(p)
env=json.loads((D/'env-l1.json').read_text());env['LEAN_PATH']=str(D/'objects')+':'+env['LEAN_PATH'];(D/'env-audit.json').write_text(json.dumps(env,indent=2)+'\n')
(D/'merged-cohort.json').write_text(json.dumps(dict(project_objects=len(rows),overlap_hash_mismatches=conflicts,policy='original prefixes retained after identical private read-only object copies'),indent=2)+'\n')
print('merged',len(rows),'project objects')
