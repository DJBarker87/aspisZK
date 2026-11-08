"""Add ONLY the header-verified compatible W4 closure to a private overlay.
The original W3/W4 inventories and every provider object stay unchanged.
"""
import json,lzma,pathlib,hashlib,shutil
P=pathlib.Path('/home/dombarker/project-offloads/codex-pv-lib-spec-20261107');E=P/'evidence'
a=json.loads(lzma.decompress((P/'W4_OBJECT_AUTHORITY.json.xz').read_bytes()));b=json.loads(lzma.decompress((P/'W3_OBJECT_AUTHORITY.json.xz').read_bytes()));g=json.loads((E/'session5-w4-import-graph.json').read_text());expected=json.loads((P/'w4-expected-source-pins.json').read_text())
def sha(p):
 with open(p,'rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
env=json.loads((P/'J-w3.json').read_text());roots=[pathlib.Path(x) for x in env['LEAN_PATH'].split(':')]+[pathlib.Path(env['LEAN_SYSROOT'])/'lib/lean'];O=P/'objects-w4-compatible';S=P/'sources-w4-compatible';O.mkdir(exist_ok=True);S.mkdir(exist_ok=True)
result=[];new=dict(b['modules'])
for row in g:
 m=row['module'];source=pathlib.Path(a['modules'][m]['path']);relative=pathlib.Path(*m.split('.'));candidates=[r/relative.with_suffix('.olean') for r in roots];target=next((c for c in candidates if c.exists()),None)
 assert sha(source)==a['modules'][m]['sha256'],m
 if target is not None:assert sha(target)==sha(source),f'cohort conflict: {m}: {target} vs {source}'
 else:
  assert m in expected and expected[m]['sha256'],f'unpinned added source {m}'
  sp=source.parent.parent/'sources'/(source.stem+'.lean')
  assert sp.exists() and sha(sp)==expected[m]['sha256'],f'added source mismatch {m}: {sp}'
  target=O/relative.with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
  if target.exists():assert sha(target)==sha(source),m
  else:shutil.copy2(source,target)
  for suffix in ['.olean.private','.olean.server','.ir']:
   original=source.with_suffix(suffix);dest=target.with_suffix(suffix)
   if original.exists():
    if dest.exists():assert sha(dest)==sha(original)
    else:shutil.copy2(original,dest)
  destsrc=S/(m+'.lean')
  if destsrc.exists():assert sha(destsrc)==sha(sp)
  else:shutil.copy2(sp,destsrc)
 result.append({'module':m,'path':str(target),'sha256':sha(target),'copied':target.is_relative_to(O),'imports':row['imports']})
 new[m]={'path':str(target),'sha256':sha(target)}
b['modules']=new;b['compatible_extension']={'authority':'original W4 ce2 source + actual OLean import-header closure','graph':str(E/'session5-w4-import-graph.json'),'overlay':str(O),'nodes':len(g)}
(P/'W3_COMPAT_OBJECT_AUTHORITY.json.xz').write_bytes(lzma.compress(json.dumps(b).encode()));(E/'session5-w4-compatible-overlay.json').write_text(json.dumps(result))
print(json.dumps({'nodes':len(g),'copied':sum(r['copied'] for r in result),'conflicts':0}))
