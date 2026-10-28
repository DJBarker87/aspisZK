from pathlib import Path
import json,subprocess,sys
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-runjoin34-20261028'
mods=json.loads((E/'data-prerequisites.json').read_text())
lo,hi,offset=map(int,sys.argv[1:])
accepted={v['module'] for d in ['pv-runjoin32-20261028','pv-runjoin33-20261028','pv-runjoin34-20261028'] for f in (R/'evidence'/d).glob('modules-*.json') for v in json.loads(f.read_text()) if v['accepted']}
pending=[m for m in mods[offset:] if m not in accepted]
for a,m in zip(range(lo,hi+1),pending):
 r=subprocess.run(['python3',str(R/'tools/pv-runjoin34-20261028/compile.py'),str(a),'0',m],cwd=R)
 if r.returncode: raise SystemExit(r.returncode)
