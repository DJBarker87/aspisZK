"""Sequential focused compilation; a refusal retries the same unlaunched ID.
compile.py enforces cooldown. A compiler failure stops the queue for inspection.
"""
from pathlib import Path
import subprocess,sys,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-world-20261028';n=int(sys.argv[1])
for m in sys.argv[2:]:
 assert n<=50499
 for retry in range(11):
  with (E/f'controller-{n}.log').open('a') as f:
   r=subprocess.run([sys.executable,str(Path(__file__).with_name('compile.py')),str(n),'R1Z/'+m],stdout=f,stderr=subprocess.STDOUT)
  print(n,m,r.returncode,flush=True)
  if r.returncode!=78:break
 if r.returncode:sys.exit(r.returncode)
 n+=1
print('next unused ID',n,flush=True)
