from pathlib import Path
import subprocess,tarfile,io
E=Path('evidence/pv-batch2-20261027/batch2c')
code="""from pathlib import Path
import sys,tarfile
D=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027')
with tarfile.open(fileobj=sys.stdout.buffer,mode='w|') as t:
 for root in list((D/'candidate').glob('batch2c-*'))+list((D/'candidate').glob('batch2b-batch2c-*'))+list(D.glob('batch2c-extraction*')):
  for p in root.rglob('*'):
   if p.is_file() and not any(x in p.parts for x in ['artifacts','diagnostics']) and p.suffix in ['.json','.log','.txt','.lean']:
    t.add(p,arcname=str(p.relative_to(D)),recursive=False)
"""
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code.encode(),capture_output=True,check=True)
with tarfile.open(fileobj=io.BytesIO(r.stdout)) as t:t.extractall(E,filter='data')
print('collected text receipts')
