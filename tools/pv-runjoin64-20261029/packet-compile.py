from pathlib import Path
import json,subprocess,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin64-20261029';T=Path(__file__).parent
a=int(sys.argv[1]);order=json.loads((E/'packet-order.json').read_text())
for m in order:
 prior=[v for p in E.glob('modules-*.json') for v in json.loads(p.read_text()) if v['module']==m and v['accepted']]
 if prior:continue
 assert a<=76096
 r=subprocess.run([sys.executable,str(T/'focused.py'),str(a),m])
 if r.returncode:raise SystemExit(r.returncode)
 a+=1
print('PACKET PREREQUISITES COMPLETE, next',a)
