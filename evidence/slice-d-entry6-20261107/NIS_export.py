from NIS_formal import *
mods=json.loads((E/'NIS_FINAL_IMPORTS.json').read_text())+json.loads((E/'NIS_RETARGET.json').read_text())['order']
srcs={m:sha((E/(m+'.lean')).read_bytes()) for m in mods}
code='''from pathlib import Path
import json,hashlib,shutil
B=Path(%r);mods=json.loads(%r);sources=json.loads(%r);cache=Path('/home/dombarker/project-offloads/codex-cx-slice-d-entry-cache-20261104');rows=[]
for m in sorted(set(mods)):
 p=B/'NIS_objects'/(m+'.olean');assert p.is_file(),m
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():rows.append({'name':z.name,'sha256':hashlib.sha256(z.read_bytes()).hexdigest(),'bytes':z.stat().st_size})
h=hashlib.sha256(json.dumps(rows,sort_keys=True).encode()).hexdigest();out=cache/('NIS_exports_20261107_'+h[:12]);out.mkdir(exist_ok=True)
for r in rows:
 src=B/'NIS_objects'/r['name'];dst=out/r['name']
 if dst.exists():assert hashlib.sha256(dst.read_bytes()).hexdigest()==r['sha256']
 else:shutil.copy2(src,dst)
manifest={'tree_sha256':h,'path':str(out),'files':rows,'source_sha256':sources,'bytes':sum(r['bytes'] for r in rows),'cache_retained':True,'closure':'NIM canonical objects and SInt2 objects retained read-only; exact Aeneas/direct dependency objects pinned by every formal receipt'}
(B/'NIS_EXPORT.json').write_text(json.dumps(manifest,indent=1)+'\\n')
print(json.dumps({'status':'PASS_EXPORT','bytes':manifest['bytes'],'tree_sha256':h,'files':len(rows)}))
'''%(B,json.dumps(mods),json.dumps(srcs))
r=run('NIS_L061','inspect','retained_export',['python3','NIS_export_host.py'],{'NIS_export_host.py':code});assert r['exit_status']==0
r=ssh('cat '+B+'/NIS_EXPORT.json');assert r.returncode==0;(E/'NIS_EXPORT.json').write_text(r.stdout)
print('PASS_RETAINED_EXPORT',flush=True)
