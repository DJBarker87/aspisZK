"""Compile newly required dictionary/source prerequisites once, topologically."""
from pathlib import Path
import json,subprocess,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin41-20261028';p=json.loads((E/'build-plan.json').read_text())
accepted={v['module'] for d in ['pv-runjoin32-20261028','pv-runjoin33-20261028','pv-runjoin34-20261028','pv-runjoin35-20261028','pv-runjoin38-20261028','pv-runjoin39-20261028','pv-runjoin40-20261028','pv-runjoin41-20261028'] for f in (R/'evidence'/d).glob('modules-*.json') for v in json.loads(f.read_text()) if v['accepted']}
seen=set();order=[]
def visit(m):
 if m in accepted or m in seen or m not in p['modules']:return
 seen.add(m)
 for d in p['modules'][m]['imports']:visit(d)
 order.append(m)
for m in sys.argv[3:]:visit(m)
(E/'source-prerequisites.json').write_text(json.dumps(order,indent=2)+'\n')
for a,m in zip(range(int(sys.argv[1]),int(sys.argv[2])+1),order):
 r=subprocess.run(['python3',str(R/'tools/pv-runjoin41-20261028/compile.py'),str(a),'0',m],cwd=R)
 if r.returncode:raise SystemExit(r.returncode)
