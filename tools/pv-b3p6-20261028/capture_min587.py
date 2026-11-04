"""Capture exact min source inputs; read-only, no compilation scope."""
from pathlib import Path
import json,lzma,subprocess,hashlib
R=Path('evidence/pv-b3p6-20261028/resume18');code='''from pathlib import Path
import json
out=[]
for v in ['1.94.1','nightly-2026-06-01']:
 p=Path('/home/dombarker/.rustup/toolchains')/(v+'-x86_64-unknown-linux-gnu')/'lib/rustlib/src/rust/library/core/src/cmp.rs'
 out.append(dict(version=v,path=str(p),source=p.read_text()))
print(json.dumps(out))
'''
rows=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True));out=[]
for row in rows:
 raw=row.pop('source').encode();p=R/'std587-source'/row['version']/'cmp.rs.xz';p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(lzma.compress(raw,preset=6));out.append(dict(**row,local_path=str(p),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw)))
(R/'MIN-SOURCE-CAPTURE-D587.json').write_text(json.dumps(out,indent=2)+'\n');print('captured two min source inputs')
