"""Collect only resumed text receipts, never keys, ELF, binaries or fixtures."""
from pathlib import Path
import json,subprocess,tarfile,io
H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-pv-batch2-20261027'
E=Path('evidence/pv-batch2-20261027/batch2b');E.mkdir(exist_ok=True)
code="""from pathlib import Path
import io,sys,tarfile
D=Path(DIR)
with tarfile.open(fileobj=sys.stdout.buffer,mode='w|') as t:
 for root in list((D/'candidate').glob('batch2b-*'))+[D/'batch2b-extraction']:
  if not root.exists():continue
  for p in root.rglob('*'):
   if not p.is_file() or any(x in p.parts for x in ['artifacts','diagnostics']):continue
   if p.suffix not in ['.json','.log','.txt','.lean']:continue
   t.add(p,arcname=str(p.relative_to(D)),recursive=False)
""".replace('DIR',repr(D))
r=subprocess.run(['ssh',H,'python3 -'],input=code.encode(),capture_output=True,check=True)
with tarfile.open(fileobj=io.BytesIO(r.stdout)) as t:t.extractall(E,filter='data')
print('text receipts collected')
