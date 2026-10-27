from pathlib import Path
import os,sys,tarfile
H=Path('/home/dombarker/project-offloads/codex-pv-quiet-20261027')
with tarfile.open(fileobj=sys.stdout.buffer,mode='w|') as archive:
 for root,dirs,files in os.walk(H):
  dirs[:]=[d for d in dirs if d not in ['target','source','bin','ledger','__pycache__']]
  for name in sorted(files):
   p=Path(root)/name
   if p.suffix in ['.json','.log','.txt','.py','.sh']:archive.add(p,arcname=str(p.relative_to(H)),recursive=False)
