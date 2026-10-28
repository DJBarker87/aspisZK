from pathlib import Path
import os,json,hashlib
R=Path('/home/dombarker/project-offloads/codex-pv-kscan-20261028');P=R.parent
roots=['codex-pv-canon-20261027/control','codex-pv-inv-20261027','codex-pv-l2-sim-20261026','codex-pv-cb-20261026','codex-pv-cb3-20261026/source-proof','codex-pv-cb3-20261026/source','codex-pv-cblib-20261027/source','codex-pv-cbmid-20261027','codex-pv-join-20261026','codex-pv-runjoin-20261026','codex-pv-srcid3-20261026','codex-cx-prover-rw-20261023/src','codex-pv-dlib-20261028/native-proof']
files={}
for root in roots:
 for d,ds,fs in os.walk(P/root):
  ds[:]=[s for s in ds if s not in ['.git','.lake','node_modules'] and 'target' not in s and 'objects' not in s and not s.startswith('evidence')]
  for f in fs:
   if f.endswith('.rs') or f in ['Cargo.toml','Cargo.lock']:
    p=Path(d)/f
    try:b=p.read_bytes()
    except OSError:continue
    files[str(p)]={'sha256':hashlib.sha256(b).hexdigest(),'text':b.decode(errors='replace')}
(R/'d347-host-sources.json').write_text(json.dumps(files)+'\n'); print(len(files))
