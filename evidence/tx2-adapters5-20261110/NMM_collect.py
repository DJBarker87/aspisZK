"""Read-only evidence recovery, then private object export after all scopes finish."""
from NMM_transport import *
import hashlib,lzma,base64
sha=lambda b:hashlib.sha256(b).hexdigest()
r=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r});names=[p for p in b.glob('NEP_*') if p.is_file()]+[p for p in b.glob('NMM_*') if p.is_file() and ('LOADED_' in p.name or 'binary_' in p.name or p.name in ['NMM_AUDIT_LINK_INPUTS.json','NMM_SCAN_BINARY.json'])]
print(json.dumps({{p.name:base64.b64encode(p.read_bytes()).decode() for p in names}}))
''');assert r.returncode==0,r.stderr
fetched=[]
for n,t in json.loads(r.stdout).items():
 raw=base64.b64decode(t);p=E/n
 if n.endswith('.txt'):
  p.with_name(n+'.xz').write_bytes(lzma.compress(raw));p.with_name(n+'.sha256').write_text(sha(raw)+'\n')
 else:p.write_bytes(raw)
 fetched.append(dict(file=n,sha256=sha(raw),bytes=len(raw)))
(E/'NMM_AUDIT_FETCH.json').write_text(json.dumps(fetched,indent=1)+'\n')
print(json.dumps(dict(fetched=len(fetched),bytes=sum(x['bytes'] for x in fetched))))
