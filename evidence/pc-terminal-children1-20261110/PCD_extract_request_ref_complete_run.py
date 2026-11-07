from PCD_formal import *
import base64,lzma
r=run('PCD_E011','extraction','POOL:314 safe unboxed reference Charon/Aeneas after standalone lock normalization and frozen-graph validation',['python3','PCD_extract_request_ref_complete.py'],{'PCD_extract_request_ref_complete.py':(E/'PCD_extract_request_ref_complete.py').read_text(),'PCD_request_ref/src/lib.rs':(E/'PCD_request_reference.rs').read_text(),'PCD_request_ref/Cargo.toml':(E/'PCD_RequestRef_Cargo.toml').read_text(),'PCD_request_ref/Cargo.lock':(E/'PCD_RequestRef_Cargo.lock').read_text()})
rr=ssh('python3',f"from pathlib import Path;import json,base64;b=Path({B!r});print(json.dumps({{n:base64.b64encode((b/n).read_bytes()).decode() for n in ['PCD_REF_CHARON_PINS.json','PCD_request_ref.llbc','PCD_REF_GRAPH_CHECK.json','PCD_REF_AENEAS_PINS.json','PCD_REF_METADATA.json','PCD_request_ref/Cargo.lock']+[str(q.relative_to(b)) for q in (b/'PCD_ref_request_extracted').rglob('*.lean')] if (b/n).is_file()}}))")
assert rr.returncode==0,rr.stderr
for n,t in json.loads(rr.stdout).items():
 raw=base64.b64decode(t)
 if n.endswith('.llbc'):(E/(n+'.xz')).write_bytes(lzma.compress(raw));(E/(n+'.sha256')).write_text(sha(raw)+'\n')
 else:
  q=E/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(raw)
print('PCD request actual selection and pinned extraction receipt recovered; no closure inferred.')
sys.exit(r['exit_status'])
