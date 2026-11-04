"""Read-only preparation for helper318 range-slice metadata; no proof credit."""
from pathlib import Path
import hashlib,json,lzma,subprocess
R=Path('evidence/pv-b3p6-20261028/resume18')
code="""from pathlib import Path
import json
rows=[]
for version in ['1.94.1','nightly-2026-06-01']:
 for name in ['slice/index.rs','ptr/const_ptr.rs']:
  path=Path('/home/dombarker/.rustup/toolchains')/(version+'-x86_64-unknown-linux-gnu')/'lib/rustlib/src/rust/library/core/src'/name
  rows.append(dict(version=version,name=name,path=str(path),source=path.read_text()))
print(json.dumps(rows))
"""
rows=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True));pins=[]
for row in rows:
 raw=row.pop('source').encode();p=R/'std581-source'/row['version']/(row['name']+'.xz');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(lzma.compress(raw,preset=6));pins.append(dict(**row,local_path=str(p),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw)))
(R/'SLICE-SOURCE-PREPARATION-D581.json').write_text(json.dumps(dict(source_capture=pins,status='PREPARATION ONLY; no parity or source-model association claimed',opaque_helper=318,remaining_assertion=[319,21975],model_draft='PV_B3P_SliceMetadata581227',compiled=False,premises_removed=[]),indent=2)+'\n')
print('captured four source inputs; preparation only')
