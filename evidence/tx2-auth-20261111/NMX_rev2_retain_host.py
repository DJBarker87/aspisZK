"""Retain revision2 separately; verify predecessor and accepted source pins."""
from pathlib import Path
import json,hashlib,lzma,os,shutil
B=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
roots=[Path(x) for x in os.environ['LEAN_PATH'].split(':')]
pre=[]
for p in [B/'NMX_PREDECESSOR_PINS.json.xz',B.parent/'codex-cx-tx2-entry5-20261110/NMN_CLOSURE_PINS.json.xz']:
 x=json.loads(lzma.decompress(p.read_bytes()));pre.extend(x if isinstance(x,list) else x['selected_objects'])
assert not [r['module'] for r in pre if r['module'].startswith('RSL_')],'Do not silently reuse revision1 canonical objects'
unique={}
for row in pre:
 key=(row['module'],''.join(Path(row['path']).suffixes))
 if key in unique:assert unique[key]['sha256']==row['sha256'],key
 else:unique[key]=row
selected=[]
for row in unique.values():
 suffix=''.join(Path(row['path']).suffixes);rel=row['module'].replace('.','/')+suffix
 p=next((r/rel for r in roots if (r/rel).is_file()),Path(row['path']))
 assert sha(p)==row['sha256'],('inherited mismatch',row['module'])
 selected.append(dict(row,path=str(p)))
mods=json.loads((B/'NMX_REV2_EXPORT_MODULES.json').read_text());out=B/'NMX_exports_revision2_20261107';out.mkdir(exist_ok=True)
accepted={}
for p in B.glob('NMX_L*/receipt.json'):
 r=json.loads(p.read_text());m=r['module'];src=B/'NMX_generated'/(m+'.lean')
 if r['kind']=='lean' and r['exit_status']==0 and src.is_file() and sha(src)==r['source_hashes'].get('NMX_generated/'+m+'.lean'):
  if m not in accepted or int(r['attempt'][-3:])>int(accepted[m]['attempt'][-3:]):accepted[m]=r
exports=[];sources=[]
for m in mods:
 rc=accepted[m];p=B/'NMX_generated'/(m+'.lean')
 sources.append(dict(module=m,path=str(p),sha256=sha(p),accepted_attempt=rc['attempt']))
 obj=B/'NMX_objects'/(m+'.olean');assert obj.is_file(),m
 for p in [obj,Path(str(obj)+'.private'),Path(str(obj)+'.server'),obj.with_suffix('.ir')]:
  if not p.is_file():continue
  q=out/p.name
  if q.exists():assert sha(q)==sha(p),q
  else:shutil.copy2(p,q)
  row=dict(module=m,path=str(q),sha256=sha(q),bytes=q.stat().st_size);exports.append(row);selected.append(dict(row,path=str(p)))
for row in json.loads((B/'NMX_REV2_CANONICAL.json').read_text()):
 m=row['module'];src=B/'NMX_R2_canonical'/(m+'.lean');assert sha(src)==row['source_sha256']
 rc=json.loads((B/row['attempt']/'receipt.json').read_text());assert rc['exit_status']==0
 sources.append(dict(module=m,path=str(src),sha256=sha(src),accepted_attempt=rc['attempt']))
 obj=B/'NMX_R2_canonical_objects'/(m+'.olean')
 for p in [obj,Path(str(obj)+'.private'),Path(str(obj)+'.server'),obj.with_suffix('.ir')]:
  if not p.is_file():continue
  q=out/p.name
  if q.exists():assert sha(q)==sha(p)
  else:shutil.copy2(p,q)
  row=dict(module=m,path=str(q),sha256=sha(q),bytes=q.stat().st_size);exports.append(row);selected.append(dict(row,path=str(p)))
write=lambda n,x:(B/n).write_text(json.dumps(x,indent=1)+'\n')
write('NMX_REV2_EXPORT.json',dict(export=str(out),files=exports,source_inputs=sources,cache_retained=True))
raw=json.dumps(dict(LEAN_PATH=os.environ['LEAN_PATH'],selected_objects=selected,own_modules=mods,canonical_revision=2)).encode()
(B/'NMX_REV2_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(B/'NMX_REV2_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
write('NMX_REV2_RETENTION.json',dict(inherited_files=len(unique),export_files=len(exports),source_files=len(sources),disk=shutil.disk_usage(B)._asdict(),deletions=0))
print(json.dumps(dict(status='PASS',inherited_files=len(unique),export_files=len(exports))))
