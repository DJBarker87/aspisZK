"""Read-only snapshot of the original W4 environment; write only SPEC dir.
No object mixing, rebuilding or provider writes. Source hashes are checked by
the local source-pin comparison before importing a new package statement.
"""
import json,pathlib,hashlib,lzma
P=pathlib.Path('/home/dombarker/project-offloads/codex-pv-lib-spec-20261107');B=pathlib.Path('/home/dombarker/project-offloads/codex-pv-w4-20261108')
def sha(p):
 with open(p,'rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
env=json.loads((B/'J.json').read_text());modules={}
for root in env['LEAN_PATH'].split(':'):
 for p in pathlib.Path(root).rglob('*.olean'):
  name=str(p.relative_to(root))[:-6].replace('/','.')
  if name not in modules:modules[name]={'path':str(p),'sha256':sha(p)}
sources={p.stem:{'path':str(p),'sha256':sha(p)} for p in (B/'sources').glob('*.lean')}
(P/'W4_OBJECT_AUTHORITY.json.xz').write_bytes(lzma.compress(json.dumps({'modules':modules,'source_environment':str(B/'J.json'),'environment':env,'source_snapshot':sources}).encode()))
print(json.dumps({'modules':len(modules),'sources':len(sources)}))
