from pathlib import Path
import sys,json,lzma,base64,hashlib
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NCL_host as h
attempts=[p.parent.name for p in sorted(E.glob('NCL_K[0-9][0-9][0-9]/receipt.json'))]
code=f'''from pathlib import Path
import json,lzma,base64,hashlib
b=Path({h.B!r});out={{}}
for a in {attempts!r}:
 for p in (b/a/'sources').rglob('*'):
  if p.is_file():out[str(p.relative_to(b))]=p.read_text()
raw=json.dumps(out).encode();packed=lzma.compress(raw,preset=6)
print(json.dumps(dict(sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),packed_bytes=len(packed),files=len(out),data=base64.b64encode(packed).decode())))
'''
r=h.remote_py(code);assert r.returncode==0,r.stderr
out=json.loads(r.stdout);raw=lzma.decompress(base64.b64decode(out.pop('data')))
assert hashlib.sha256(raw).hexdigest()==out['sha256']
for n,s in json.loads(raw).items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
(E/'NCL_SOURCE_RECOVERY.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
