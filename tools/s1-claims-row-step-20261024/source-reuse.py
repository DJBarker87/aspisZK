#!/usr/bin/env python3
"""Store unchanged compiled source inputs as exact immutable git-blob references."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];P=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/s1-claims-row-step-20261024';rev='25866ec331cc7ce27dd9956609c11d32fa8fa58a'
assert not (P/'source-reuse.json').exists();rows={}
for dep in (P/'dependencies').iterdir():
 root=json.loads((dep/'source-root.json').read_text())['root']
 if '/codex-cx-repin-s6-20261020/src/' in root:prefix=root.split('/codex-cx-repin-s6-20261020/src/',1)[1]
 elif root.endswith('/frozen-probe'):prefix='crates/aspis-r1-cost-probe'
 elif root.endswith('/frozen-source/crates/aspis-statement'):prefix='crates/aspis-statement'
 else:raise AssertionError(root)
 for p in dep.rglob('*'):
  if not p.is_file() or p.name=='source-root.json':continue
  path=prefix+'/'+str(p.relative_to(dep));q=subprocess.run(['git','-C',str(R),'rev-parse',rev+':'+path],capture_output=True,text=True)
  if q.returncode:continue
  oid=q.stdout.strip();blob=subprocess.check_output(['git','-C',str(R),'cat-file','blob',oid]);actual=p.read_bytes()
  if actual!=blob:continue
  rel=str(p.relative_to(P));rows[rel]=dict(revision=rev,path=path,git_blob=oid,sha256=hashlib.sha256(blob).hexdigest(),bytes=len(blob))
assert rows
(P/'source-reuse.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',qualification='Storage deduplication only: every referenced compiled input is byte-identical to this immutable source blob. Native original manifest/input hashes are unchanged; harness modifications remain physical files.',files=rows),indent=2)+'\n')
# Only remove our newly staged duplicate source-code files, never keys or live trees.
for rel in rows:
 p=P/rel;assert p.is_relative_to(P/'dependencies') and p.suffix in ['.rs','.toml','.py','.lock']
 subprocess.run(['git','-C',str(R),'restore','--staged','--',str(p.relative_to(R))],check=True)
 p.unlink()
print(json.dumps(dict(reused_files=len(rows),reused_bytes=sum(r['bytes'] for r in rows.values()))))
