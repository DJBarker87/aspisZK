from NET_remote import *
import hashlib
assert not (E/'NET_ACTIVE.json').exists()
modules=sorted({json.loads(p.read_text())['module'] for p in E.glob('NET_L*/receipt.json') if json.loads(p.read_text())['exit_status']==0})
C='/home/dombarker/project-offloads/codex-cx-slice-q-compose3-cache-20261029'
code=f'''from pathlib import Path
import hashlib,json,shutil
b=Path({B!r});cache=Path({C!r});assert not cache.is_symlink()
export=cache/'NET_exports_20261104';records=[];originals=[]
for mod in {modules!r}:
 assert all(c.isalnum() or c in '._' for c in mod) and not mod.startswith('Aeneas')
 main=b/(mod.replace('.','/')+'.olean');assert main.is_file(),str(main)
 for p in sorted(main.parent.glob(main.name+'*')):
  if not p.is_file():continue
  data=p.read_bytes();h=hashlib.sha256(data).hexdigest();q=export/p.relative_to(b);q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  else:q.write_bytes(data)
  assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  records.append(dict(module=mod,source=str(p),destination=str(q),sha256=h,bytes=len(data)));originals.append(p)
out=dict(cache=str(cache),export=str(export),objects=records,policy='Own cache retained; unchanged peer caches and coherent/Aeneas objects untouched; exact byte copies',cleanup=[])
manifest=b/'NET_CACHE_EXPORTS.json';manifest.write_text(json.dumps(out,indent=1)+'\\n')
for p in originals:p.unlink()
out['compiled_scratch_removed']=len(originals)
for name in ['NET_target','NET_tmp']:
 p=b/name;assert p.parent==b and not p.is_symlink()
 if not p.exists():continue
 possible=[]
 for f in p.rglob('*.json'):
  if f.stat().st_size>200000:continue
  try:value=json.loads(f.read_text())
  except (ValueError,UnicodeDecodeError):continue
  if isinstance(value,list) and len(value)==64 and all(isinstance(x,int) and 0<=x<256 for x in value):possible.append(str(f))
 if possible:
  out['cleanup'].append(dict(path=str(p),removed=False,reason='Possible key file retained; no key cleanup authorized',files=possible));continue
 size=sum(f.stat().st_size for f in p.rglob('*') if f.is_file() and not f.is_symlink());shutil.rmtree(p)
 out['cleanup'].append(dict(path=str(p),removed=True,bytes=size))
manifest.write_text(json.dumps(out,indent=1)+'\\n');print(json.dumps(out))
'''
r=ssh('NET_CACHE_FINISH','python3',code,submitted=True)
if r.returncode!=0:
 (E/'NET_CACHE_FINISH_UNRESOLVED.json').write_text(json.dumps(dict(exit_status=r.returncode,stderr=r.stderr,host_manifest=B+'/NET_CACHE_EXPORTS.json',policy='Recover read-only; never resubmit a submitted cleanup'),indent=1)+'\n');raise SystemExit('Recover host cache manifest read-only')
(E/'NET_CACHE_EXPORTS.json').write_text(r.stdout)
x=json.loads(r.stdout);print(json.dumps(dict(objects=len(x['objects']),compiled_scratch_removed=x['compiled_scratch_removed'],cleanup=x['cleanup'])))
