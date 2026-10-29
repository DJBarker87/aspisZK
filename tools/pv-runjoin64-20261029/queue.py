from pathlib import Path
import subprocess,sys,json
R=Path(__file__).resolve().parents[2];T=Path(__file__).parent;E=R/'evidence/pv-runjoin64-20261029';a=int(sys.argv[1])
for m in sys.argv[2:]:
 assert 76000<=a<=76096
 accepted=[v for p in E.glob('modules-*.json') for v in json.loads(p.read_text()) if v['accepted'] and v['module']==m]
 if accepted:continue
 r=subprocess.run([sys.executable,str(T/'focused.py'),str(a),m])
 if r.returncode:raise SystemExit(r.returncode)
 a+=1
print('NEXT',a,flush=True)
