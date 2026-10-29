"""Sequential focused targets; each invokes existing task launcher once."""
from pathlib import Path
import subprocess,sys,json
R=Path(__file__).resolve().parents[2]
for line in Path(sys.argv[1]).read_text().splitlines():
 if not line.strip() or line.startswith('#'):continue
 n,m=line.split()
 r=subprocess.run([sys.executable,str(R/'tools/pv-ownb-20261029/lean.py'),n,m],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (R/'evidence/pv-ownb-20261029'/f'launch-{n}.log').write_text(r.stdout)
 print(n,m,r.returncode,flush=True)
 if r.returncode:print(r.stdout[-6000:],flush=True);sys.exit(r.returncode)
