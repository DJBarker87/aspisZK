from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-multiproof4-20261108';C='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJV_20261108'
inv=json.loads((E/'NJV_PROOF_INVENTORY.json').read_text());modules=list(inv['modules'])+['NJV_COMBINED_IMPORT']
code=f'''from pathlib import Path
import hashlib,json,shutil,os
b=Path({B!r});dst=Path({C!r})/'NJV_exports_20261108';dst.mkdir(parents=True,exist_ok=True)
items=[]
for module in {modules!r}:
 p=b/'NJV_objects'/(module+'.olean');assert p.is_file(),p
 for f in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not f.is_file():continue
  q=dst/f.name;data=f.read_bytes();h=hashlib.sha256(data).hexdigest()
  if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  else:shutil.copy2(f,q)
  assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  items.append(dict(module=module,source=str(f),path=str(q),sha256=h,size=len(data)))
audit=[]
for name in ['NJV_Driver','NJV_ProofDriver']:
 p=b/'NJV_native'/name;assert p.is_file();audit.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size))
r=json.loads((b/'NJV_L068'/'receipt.json').read_text());pins=r.get('deps_fingerprint',{{}}).get('selected_objects',{{}})
lib={{k:v for k,v in pins.items() if '/Aeneas/' in k or '/AeneasMeta/' in k or k.endswith('/Aeneas.olean') or k.endswith('/AeneasMeta.olean')}}
out=dict(workspace=str(b),cache={C!r},export=str(dst),modules={modules!r},files=items,total_bytes=sum(x['size'] for x in items),audit_executables=audit,library_pins=lib,proof_inventory={inv!r},target_established=False)
(b/'NJV_EXPORT.json').write_text(json.dumps(out,indent=2)+'\\n');print(json.dumps(out))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NJV_export_transport.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr)))
assert r.returncode==0,'Export transport failure: recover host NJV_EXPORT.json read-only; never resubmit a proof'
x=json.loads(r.stdout);(E/'NJV_EXPORT.json').write_text(json.dumps(x,indent=2)+'\n')
env=json.loads((E/'NJV_ENV.json').read_text());env['LEAN_PATH']=':'.join([x['export']]+[p for p in env['LEAN_PATH'].split(':') if p!=B+'/NJV_objects']);(E/'NJV_ENV_FINAL.json').write_text(json.dumps(env,indent=2)+'\n')
print(f'NJV retained export: {len(x["files"])} files, {x["total_bytes"]} bytes; no cache removed')
