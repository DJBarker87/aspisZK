"""Read-only cohort comparison; never replace provider or existing objects."""
import pathlib,json,lzma,hashlib,shutil
P=pathlib.Path('/home/dombarker/project-offloads/codex-pv-lib-spec-20261107');E=P/'evidence'
sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
a=json.loads(lzma.decompress((P/'LANEA_OBJECT_AUTHORITY.json.xz').read_bytes()))['modules']
b=json.loads(lzma.decompress((P/'W3_COMPAT_OBJECT_AUTHORITY.json.xz').read_bytes()))
g=json.loads((E/'session9-lanea-import-graph.json').read_text())
env=json.loads((P/'J-w3.json').read_text());roots=[pathlib.Path(r) for r in env['LEAN_PATH'].split(':')]+[pathlib.Path(env['LEAN_SYSROOT'])/'lib/lean']
rows=[];conflicts=[]
for row in g:
 m=row['module'];rel=pathlib.Path(*m.split('.')).with_suffix('.olean')
 existing=next((r/rel for r in roots if (r/rel).exists()),None)
 source=pathlib.Path(a[m]['path']) if m in a else pathlib.Path(env['LEAN_SYSROOT'])/'lib/lean'/rel
 h=sha(source)
 if m in a:assert h==a[m]['sha256'],m
 item={'module':m,'lanea':str(source),'sha256':h,'existing':str(existing) if existing else None,'imports':row['imports']}
 if existing is not None and sha(existing)!=h:conflicts.append(item)
 rows.append(item)
(E/'SESSION9_COHORT_COMPARISON.json').write_text(json.dumps({'conflicts':conflicts,'closure':rows},indent=2))
print(json.dumps({'closure':len(rows),'new':sum(x['existing'] is None for x in rows),'conflicts':[x['module'] for x in conflicts]}))
if conflicts:raise SystemExit(2)
O=P/'objects-lanea-compatible';O.mkdir(exist_ok=True)
for row in rows:
 m=row['module'];source=pathlib.Path(row['lanea']);target=pathlib.Path(row['existing']) if row['existing'] else O/pathlib.Path(*m.split('.')).with_suffix('.olean')
 if row['existing'] is None:
  target.parent.mkdir(parents=True,exist_ok=True)
  for suffix in ['.olean','.olean.private','.olean.server','.ir']:
   original=source.with_suffix(suffix);dest=target.with_suffix(suffix)
   if original.exists():
    if dest.exists():assert sha(dest)==sha(original),m
    else:shutil.copy2(original,dest)
 b['modules'][m]={'path':str(target),'sha256':row['sha256']}
(P/'W3_LANEA_OBJECT_AUTHORITY.json.xz').write_bytes(lzma.compress(json.dumps(b).encode()))
