from NJN_transport import *
import lzma,base64,hashlib
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,lzma,base64
b=Path({B!r});out=[]
for d in sorted(b.glob('NJN_[KL][0-9][0-9][0-9]')):
 if not d.is_dir():continue
 for p in d.rglob('*.log'):
  if 'sources' in p.relative_to(d).parts:continue
  raw=p.read_bytes();out.append(dict(path=str(p.relative_to(b)),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),data=base64.b64encode(lzma.compress(raw)).decode()))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
changes=[];rows=[]
for x in json.loads(r.stdout):
 p=E/x['path'];z=p.with_name(p.name+'.xz');h=p.with_name(p.name+'.sha256');data=base64.b64decode(x.pop('data'))
 if h.exists() and h.read_text().strip()!=x['sha256']:changes.append(dict(path=x['path'],old=h.read_text().strip(),actual=x['sha256']))
 assert hashlib.sha256(lzma.decompress(data)).hexdigest()==x['sha256']
 z.write_bytes(data);h.write_text(x['sha256']+'\n');rows.append(x)
(E/'NJN_RAW_LOGS.json').write_text(json.dumps(dict(files=rows,normalized_log_corrections=changes,reruns=0),indent=1)+'\n')
print('NJN raw byte logs preserved; corrections='+str(len(changes)))
