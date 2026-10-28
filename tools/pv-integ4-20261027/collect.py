"""Collect text receipts only, excluding keys, binaries, compiler caches and IR."""
from pathlib import Path
import subprocess,sys,io,tarfile,shlex
D='/home/dombarker/project-offloads/codex-pv-integ4-20261027'; E=Path('evidence/pv-integ4-20261027')
code='''from pathlib import Path
import tarfile,sys
H=Path(ROOT)
with tarfile.open(fileobj=sys.stdout.buffer,mode='w|') as t:
 for rel in LABELS:
  p=H/rel
  for f in ([p] if p.is_file() else p.rglob('*')):
   r=f.relative_to(H)
   if not f.is_file() or 'keypair' in f.name:continue
   if f.suffix not in ('.json','.jsonl','.log','.txt'):continue
   if any(x in r.parts for x in ['compiler-output','artifacts','source','native-target','bin']):continue
   t.add(f,arcname=str(r),recursive=False)
'''.replace('ROOT',repr(D)).replace('LABELS',repr(sys.argv[1:]))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,check=True)
with tarfile.open(fileobj=io.BytesIO(r.stdout)) as t:t.extractall(E,filter='data')
