"""Retain text receipts and a streaming SHA256 manifest, then remove only this corpus."""
from pathlib import Path
import hashlib,json,shutil,os,re
H=Path('/home/dombarker/project-offloads/codex-pv-op223-20261027');C=H/'corpus-2000';O=H/'corpus-evidence'
s=json.loads((C/'pipeline-final.json').read_text());assert s['complete'] and s['passed'] and s['completed_pairs']==1000
assert not (C/'pipeline-failure.json').exists()
O.mkdir(exist_ok=False)
files=sorted(p for p in C.rglob('*') if p.is_file())
# These names are precisely gate outputs. Never clean up account/wallet keys.
for p in files:
 n=p.name
 assert n in {'proof.bin','public.bin','oracle.bin','result.json'} or n.endswith('.burn') or re.fullmatch(r'(comparison-\d+\.json|run-\d+-(baseline|candidate)\.log|compare-\d+\.log|pipeline-[a-z-]+\.jsonl?)',n),p
with (O/'sha256-manifest.jsonl').open('w') as out:
 for p in files:
  h=hashlib.sha256()
  with p.open('rb') as f:
   for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
  out.write(json.dumps(dict(path=str(p.relative_to(C)),bytes=p.stat().st_size,sha256=h.hexdigest()))+'\n')
  if p.name.endswith(('.json','.jsonl','.log')):
   q=O/p.relative_to(C);q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
(O/'cleanup.json').write_text(json.dumps(dict(corpus=str(C),files=len(files),bytes=sum(p.stat().st_size for p in files),manifest_sha256=hashlib.sha256((O/'sha256-manifest.jsonl').read_bytes()).hexdigest(),retained='All text results/comparisons/logs and manifest; no private wallet/account keys present',deleted_keys=0),indent=2)+'\n')
for p in sorted(C.rglob('*'),reverse=True):
 if p.is_dir():os.chmod(p,0o700)
os.chmod(C,0o700);shutil.rmtree(C)
print('Corpus removed; receipts and SHA256 manifest retained in',O)
