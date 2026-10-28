from pathlib import Path
import json,subprocess,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin23-20261027'
rows=json.loads((E/'admission-build-order.json').read_text())
a=int(sys.argv[1]);start=int(sys.argv[2])
for row in rows[start:]:
 print('NEXT',a,row['module'],flush=True)
 p=subprocess.run([sys.executable,str(R/'tools/pv-runjoin23-20261027/check.py'),str(a),row['module'],row['path']],cwd=R)
 if p.returncode:sys.exit(p.returncode)
 a+=1
