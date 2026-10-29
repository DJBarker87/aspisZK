"""Recover recorded translator source into the new job-owned checkout only."""
from pathlib import Path
import hashlib,json,shutil,subprocess
H=Path('/home/dombarker/project-offloads/codex-pv-cx-20261029/resume-ae1')
P=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/rng-extractor')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
x=json.loads((P/'base-provenance.json').read_text())
rows=[]
for rel,pin in x['source_manifest'].items():
 p=H/'aeneas'/rel
 if 'sha256' in pin: rows.append(dict(path=rel,expected=pin['sha256'],actual=sha(p),equal=sha(p)==pin['sha256']))
assert all(r['equal'] for r in rows),[r for r in rows if not r['equal']]
shutil.copytree(P/'charon',H/'charon',ignore=shutil.ignore_patterns('_build','.git','target'))
(H/'aeneas/charon').unlink(missing_ok=True)
(H/'aeneas/charon').symlink_to('../charon')
for name in ['accepted-extensions.patch','historical-extensions.patch','extension-archive-difference.diff','opam-packages.txt','ocaml-version.txt','dune-version.txt']:
 shutil.copy2(P/name,H/name)
(H/'source-recovery.json').write_text(json.dumps(dict(base_revision=x['base_revision'],historical_binary=x['installed_binary'],patch=sha(H/'accepted-extensions.patch'),files=rows,all_equal=True,source_revision='570c0008098b8cc23d16d86f9edb0c2a41b0e118',note='Fresh upstream b59d5188 checkout plus retained accepted-extensions patch; every regular source file matches original source provenance. No edits to installed tools.'),indent=2)+'\n')
