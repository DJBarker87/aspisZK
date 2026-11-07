"""Read-only closure pinning, own export, and strict final evidence check."""
from pathlib import Path
import json,hashlib,lzma,shutil,sys
B=Path.cwd();mode=sys.argv[1];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
roots=json.loads((B/'NMS_R2_AUDIT_ROOTS.json').read_text());expected={n for g in roots['groups']for n in g}
actual=[];allowed={'propext','Quot.sound','Classical.choice'}
for i,group in enumerate(roots['groups']):
 r=json.loads((B/'NMS_audit'/('R2_batch'+str(i))/('proof'+str(i)+'.json')).read_text())
 assert r['exit_status']==0
 got=r['results'];assert [x['root']for x in got]==group,(i,group,got)
 for x in got:
  assert x['equal'] and set(x['walked_axioms'])==set(x['collect_axioms'])<=allowed,x
  actual.append(x['root'])
assert len(actual)==len(set(actual)) and set(actual)==expected
scan=[json.loads(l)for l in (B/'NMS_R2_LOADED_scan.jsonl').read_text().splitlines()]
assert all(x['imports_match']and not x['dangling']and not x['duplicate_owners']for x in scan)
# Compare every current accepted module's pinned direct imports/library objects,
# as well as the selected runtime closure. Hash each immutable path once per check.
checked={}
for source in roots['source_acceptance']:
 receipt=json.loads((B/source['receipt']).read_text())
 assert receipt['exit_status']==0
 for name,pin in receipt['deps_fingerprint']['selected_objects'].items():
  p=Path(pin['path'])
  if str(p)not in checked:checked[str(p)]=sha(p)
  assert checked[str(p)]==pin['sha256'],(source['module'],str(p),'compiled dependency drift')
export=B/'NMS_R2_exports_20261107';path=B/'NMS_R2_CLOSURE_PINS.json.xz'
if mode=='export':
 env=json.loads((B/'NMS_R2_EXPORT_ENV.json').read_text());search=env['LEAN_PATH'].split(':');pins=[]
 source={x['module']:x for x in roots['source_acceptance']}
 for row in scan:
  module=row['module'];rel=module.replace('.','/')+'.olean'
  obj=next((Path(r)/rel for r in search if (Path(r)/rel).is_file()),None)
  assert obj is not None,module
  objects=[]
  for p in [obj,Path(str(obj)+'.private'),Path(str(obj)+'.server'),obj.with_suffix('.ir')]:
   if p.is_file():
    item=dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size)
    if module.startswith('NMS_R2')or module.startswith('RSL_'):
     dst=export/'objects'/p.relative_to(obj.parents[len(Path(rel).parts)-1])
     dst.parent.mkdir(parents=True,exist_ok=True)
     if dst.exists():assert sha(dst)==item['sha256']
     else:shutil.copy2(p,dst)
     item['export_path']=str(dst);assert sha(dst)==item['sha256']
    objects.append(item)
  pin=dict(module=module,objects=objects)
  if module in source:
   pin['source_acceptance']=source[module]
   p=B/'NMS_generated'/(module.replace('.','/')+'.lean')
   assert sha(p)==source[module]['source_sha256'],module
   dst=export/'sources'/(module+'.lean');dst.parent.mkdir(parents=True,exist_ok=True)
   if dst.exists():assert sha(dst)==sha(p)
   else:shutil.copy2(p,dst)
  pins.append(pin)
 raw=(json.dumps(pins,indent=1)+'\n').encode();path.write_bytes(lzma.compress(raw));(B/'NMS_R2_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
 (B/'NMS_R2_EXPORT.json').write_text(json.dumps(dict(export=str(export),audit_executable_sha256=sha(B/'NMS_native/NMS_R2Driver'),audit_executable_bytes=(B/'NMS_native/NMS_R2Driver').stat().st_size,modules=len(scan),roots=len(actual),closure_sha256=hashlib.sha256(raw).hexdigest(),no_row_credit=True),indent=1)+'\n')
elif mode=='verify':
 raw=lzma.decompress(path.read_bytes());assert hashlib.sha256(raw).hexdigest()==(B/'NMS_R2_CLOSURE_PINS.json.sha256').read_text().strip()
 for pin in json.loads(raw):
  for p in pin['objects']:
   assert sha(Path(p['path']))==p['sha256']
   if 'export_path'in p:assert sha(Path(p['export_path']))==p['sha256']
else:raise ValueError(mode)
result=dict(status='PASS',mode=mode,roots=len(actual),modules=len(scan),compiled_dependency_objects=len(checked),standard_axioms_only=True,no_duplicate_roots=True,no_dangling=True,no_row_credit=True)
(B/('NMS_R2_RETENTION_'+mode+'.json')).write_text(json.dumps(result,indent=1)+'\n');print(json.dumps(result))
