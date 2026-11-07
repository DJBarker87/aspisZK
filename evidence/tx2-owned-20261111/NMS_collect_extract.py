from NMS_transport import *
import base64
kind=__import__('sys').argv[1]
r=ssh('python3',f'''from pathlib import Path
import json,base64,lzma,hashlib
b=Path({B!r});d=b/{('NMS_extract_'+kind)!r};out={{}}
for p in d.rglob('*'):
 if not p.is_file():continue
 n=str(p.relative_to(b));raw=p.read_bytes()
 if p.suffix in ['.llbc','.log'] or len(raw)>1000000:
  out[n+'.xz']=base64.b64encode(lzma.compress(raw)).decode();out[n+'.sha256']=base64.b64encode((hashlib.sha256(raw).hexdigest()+'\\n').encode()).decode()
 else:out[n]=base64.b64encode(raw).decode()
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
for n,v in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(v))
print('Collected '+kind+' outputs')
