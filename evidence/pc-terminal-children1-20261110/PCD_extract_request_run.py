from PCD_formal import *
import base64,lzma
r=run('PCD_E008','extraction','POOL:314 actual frozen wrapper Charon-only; reuse optimized objects',['python3','PCD_extract_request.py'],{'PCD_extract_request.py':(E/'PCD_extract_request.py').read_text()})
rr=ssh('python3',f"from pathlib import Path;import json,base64;b=Path({B!r});print(json.dumps({{n:base64.b64encode((b/n).read_bytes()).decode() for n in ['PCD_REQUEST_CHARON_PINS.json','PCD_frozen_request.llbc'] if (b/n).is_file()}}))")
assert rr.returncode==0,rr.stderr
for n,t in json.loads(rr.stdout).items():
 raw=base64.b64decode(t)
 if n.endswith('.llbc'):(E/(n+'.xz')).write_bytes(lzma.compress(raw));(E/(n+'.sha256')).write_text(sha(raw)+'\n')
 else:(E/n).write_bytes(raw)
print('PCD request actual selection and pinned extraction receipt recovered; no closure inferred.')
sys.exit(r['exit_status'])
