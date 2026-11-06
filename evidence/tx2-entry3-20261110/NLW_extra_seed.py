from NLW_transport import *
import lzma,base64,hashlib
admission('NLW_S003')
x=json.loads(lzma.decompress((E.parent/'tx2-entry2-20261110/NLM_NATIVE_EXTRA_INPUTS.json.xz').read_bytes()))
r=ssh('python3',f"""from pathlib import Path
import json,base64,hashlib
b=Path({B!r});x=json.loads({json.dumps(x)!r});rows=[]
for n,v in x.items():
 raw=base64.b64decode(v['data']);p=b/'NLW_src'/n;p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():assert p.read_bytes()==raw,n
 else:p.write_bytes(raw)
 rows.append(dict(path=n,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest()))
print(json.dumps(rows))
""")
assert r.returncode==0,r.stderr
(E/'NLW_EXTRA_SEED.json').write_text(r.stdout)
print(json.dumps(dict(files=len(x),bytes=sum(v['bytes'] for v in x.values()))))
