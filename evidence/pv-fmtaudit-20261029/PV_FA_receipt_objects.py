from pathlib import Path
import json,subprocess
P=Path(__file__).parent;rows=json.loads((P/'claim-audit-dispositions.json').read_text());out=[]
for r in rows:
 a=r.get('selected_standard_audit');records=[]
 if a:
  mod=r['theorem'].rsplit('.',1)[0];rel=mod.replace('.','/')+'.olean'
  for status in a['receipt_status']:
   res=subprocess.run(['git','show',a['ref']+':'+status['path']],capture_output=True)
   if res.returncode:continue
   try:rec=json.loads(res.stdout)
   except Exception:continue
   if not isinstance(rec,dict):continue
   cmd=rec.get('command',rec.get('target',[]));paths=[];envs=[]
   for v in cmd:
    if not isinstance(v,str):continue
    if v.endswith('.json')and any(s in v for s in ['env','J.json']):envs.append(v)
    if v.endswith('/'+rel):paths.append(dict(path=v,sha256=rec.get('object_sha256')if str(rec.get('module','')).replace('/','.')==mod else None))
   def walk(v):
    if isinstance(v,dict):
     for k,x in v.items():
      if isinstance(x,str)and x.endswith('/'+rel):paths.append(dict(path=x,sha256=v.get('object_sha256',v.get('sha256'))))
      yield from walk(x)
    elif isinstance(v,list):
     for x in v:yield from walk(x)
   list(walk(rec))
   # Imported closing modules live in the compiler's recorded output root.
   for i,v in enumerate(cmd):
    if isinstance(v,str)and v.endswith('/run2.py')and len(cmd)>i+2:
     paths.append(dict(path=cmd[i+2]+'/'+rel,sha256=None))
   records.append(dict(receipt=status['path'],ref=a['ref'],paths=paths,envs=envs,recorded_module=rec.get('module')))
 out.append(dict(id=r['id'],theorem=r['theorem'],records=records))
(P/'claim-recorded-object-paths.json').write_text(json.dumps(out,indent=1));print('rows with direct paths',sum(any(y['paths']for y in x['records'])for x in out))
