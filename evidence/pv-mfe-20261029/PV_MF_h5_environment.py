from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-mfe-20261029');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();env=json.load(open(D/'h5-preflight-input.json'))['environment'];roots=[D.parent/'codex-pv-replay-20261027/objects']+[Path(x) for x in env['LEAN_PATH'].split(':')];ext=json.load(open(D.parent/'codex-pv-mfb-20261029/external-object-manifest.json'));added=[]
for v in ext:
 rel=v['module'].replace('.','/')+'.olean';p=next((r/rel for r in roots if (r/rel).exists()),None);assert p and sha(p)==v['object_sha256'];q=D/'h5-objects'/rel;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():q.symlink_to(p);added.append(rel)
(D/'environment-correction-70320.json').write_text(json.dumps(dict(failed_attempt=70320,failure_class='before elaboration: missing Aeneas namespace root companion',next_attempt=70321,source_unchanged=True,correction='Link all h4-pinned external namespace companions into private h5 output overlay; no historical object changed',external_verified=len(ext),links_added=added),indent=2)+'\n');print('external links',len(added))
