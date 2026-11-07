from NMX_formal import *
exports=[]
for rel in ['lib-20261111/LIB_EXPORT.json','libb-20261111/LIBB_EXPORT.json']:
 x=json.loads((E.parent/rel).read_text()); rows=x.get('objects',x.get('files',[]))
 exports.extend(row for row in rows if Path(row['path']).name.startswith(('LIB_','LIBB_')))
script='''from pathlib import Path
import json,hashlib,shutil
b=Path.cwd();rows=json.loads(%r);out=[]
for row in rows:
 p=Path(row['path']);h=hashlib.sha256(p.read_bytes()).hexdigest();assert h==row['sha256'],p
 q=b/'NMX_LIBB_seed'/p.name;q.parent.mkdir(exist_ok=True)
 if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h,q
 else:shutil.copy2(p,q)
 out.append(dict(source=str(p),copy=str(q),sha256=h,bytes=q.stat().st_size))
(b/'NMX_LIBB_SEED.json').write_text(json.dumps(out,indent=1)+'\\n')
print(json.dumps(dict(files=len(out),deletions=0,status='PASS')))
''' % json.dumps(exports)
r=run('NMX_L944','inspect','NMX_LIBB_seed',['python3','NMX_registry_libb_seed_host.py'],{'NMX_registry_libb_seed_host.py':script})
assert r['exit_status']==0
z=ssh('cat '+B+'/NMX_LIBB_SEED.json');assert z.returncode==0
(E/'NMX_LIBB_SEED.json').write_text(z.stdout)
env=json.loads((E/'NMX_R3_REGISTRY_ENV.json').read_text());roots=env['LEAN_PATH'].split(':');roots.insert(0,B+'/NMX_LIBB_seed');env['LEAN_PATH']=':'.join(dict.fromkeys(roots));(E/'NMX_R3_REGISTRY_ENV.json').write_text(json.dumps(env,indent=1)+'\n')
