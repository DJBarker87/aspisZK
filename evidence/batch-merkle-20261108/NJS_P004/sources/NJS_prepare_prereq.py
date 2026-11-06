from pathlib import Path
import hashlib,json
E=Path.cwd();src=json.loads((E/'NJS_PREREQUISITE_INPUTS.json').read_text());out=[]
for m,x in src.items():
 raw=x['content'].encode();assert hashlib.sha256(raw).hexdigest()==x['sha256'];assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==x['git_blob']
 p=E/x['host_source'];p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():assert p.read_bytes()==raw
 else:p.write_bytes(raw)
 out.append(dict(module=m,path=str(p),sha256=x['sha256'],bytes=len(raw)))
(E/'NJS_PREREQUISITE_STAGE.json').write_text(json.dumps(out,indent=2)+'\n');print('staged9 unchanged missing prerequisites; no compiler')
