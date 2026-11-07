from PCD_formal import *
import base64,lzma
r=run('PCD_E012','extraction','Remaining five class-B actual frozen wrappers; CLOSED/open child bodies opaque, no child re-ownership',['python3','PCD_extract_batch.py'],{'PCD_extract_batch.py':(E/'PCD_extract_batch.py').read_text()})
rr=ssh('python3',f"from pathlib import Path;import json,base64;b=Path({B!r});print(json.dumps({{n:base64.b64encode((b/n).read_bytes()).decode() for n in ['PCD_BATCH_CHARON_PINS.json','PCD_BATCH_AENEAS_PINS.json','PCD_terminal_batch.llbc']+[str(q.relative_to(b)) for q in (b/'PCD_terminal_batch_extracted').rglob('*.lean')] if (b/n).is_file()}}))")
assert rr.returncode==0,rr.stderr
for n,t in json.loads(rr.stdout).items():
 raw=base64.b64decode(t)
 if n.endswith('.llbc'):(E/(n+'.xz')).write_bytes(lzma.compress(raw));(E/(n+'.sha256')).write_text(sha(raw)+'\n')
 else:
  q=E/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(raw)
print('PCD request actual selection and pinned extraction receipt recovered; no closure inferred.')
sys.exit(r['exit_status'])
