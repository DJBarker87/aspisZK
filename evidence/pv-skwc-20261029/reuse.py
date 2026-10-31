from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-skwc-20261029'); B=D.parent/'codex-pv-skwb-20261029'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
env=json.loads((B/'env-J.json').read_text()); rows=[]
# Recheck the previously established complete h6 staging, including companions.
for m,r in json.loads((B/'staging.json').read_text())['staged'].items():
 p=B/'objects'/(m.replace('.','/')+'.olean'); assert sha(p)==r['sha256'],m
 for q,h in r['companions'].items(): assert sha(Path(q))==h,q
 rows.append(dict(module=m,sha256=sha(p),authority='pv-skwb/staging.json h6'))
for rp in sorted(B.glob('lean*-receipt.json')):
 r=json.loads(rp.read_text())
 if r['exit']!=0:continue
 p=B/'objects'/(r['module'].replace('.','/')+'.olean'); assert sha(p)==r['object_sha256'],r['module']
 for hs in r['dependency_objects'].values():
  for q,h in hs.items():assert sha(Path(q))==h,q
 rows.append(dict(module=r['module'],sha256=sha(p),authority=str(rp),source_sha256=r['source_sha256']))
paths=[Path(p) for p in env['LEAN_PATH'].split(':')]
for r in json.loads((D.parent/'codex-pv-diag5-20261029/external-authority.json').read_text()):
 m=r['module'].replace('/','.');p=next(p/(m.replace('.','/')+'.olean') for p in paths if (p/(m.replace('.','/')+'.olean')).exists());assert sha(p)==r['object_sha256'],m
# Copy no binaries: stage readonly links in a single private root, preserving package layout.
for p in (B/'objects').rglob('*'):
 if not p.is_file():continue
 q=D/'objects'/p.relative_to(B/'objects');q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():q.symlink_to(p)
env['LEAN_PATH']=str(D/'objects')+':'+env['LEAN_PATH'];(D/'env-J.json').write_text(json.dumps(env,indent=2)+'\n')
(D/'reuse-verification.json').write_text(json.dumps(dict(toolchain=env['ELAN_TOOLCHAIN'],prior_prefix=paths[0].as_posix(),new_prefix=str(D/'objects'),policy='identical objects/companions and import cohort; private package-root alias only',checks=rows,external_authority='codex-pv-diag5-20261029/external-authority.json',all_match=True),indent=2)+'\n')
(D/'environment-corrections.json').write_bytes((B/'environment-corrections.json').read_bytes())
print('verified',len(rows),'cached project entries; no dependencies rebuilt')
