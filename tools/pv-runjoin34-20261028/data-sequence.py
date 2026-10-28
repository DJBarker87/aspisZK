from pathlib import Path
import json,subprocess,sys
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-runjoin34-20261028'
mods=json.loads((E/'data-prerequisites.json').read_text())
lo,hi,offset=map(int,sys.argv[1:])
for a,m in zip(range(lo,hi+1),mods[offset:]):
 r=subprocess.run(['python3',str(R/'tools/pv-runjoin34-20261028/compile.py'),str(a),'0',m],cwd=R)
 if r.returncode: raise SystemExit(r.returncode)
