"""Compile changed, committed proof targets in dependency order without rebuilding accepted sources."""
from pathlib import Path
import subprocess,sys,json,hashlib
R=Path(__file__).resolve().parents[2];T=Path(__file__).parent;E=R/'evidence/pv-runjoin46-20261028';a=int(sys.argv[1])
labels=sys.argv[2:] or ['Carrier','Map','Scalar','Complex','Quartic','Product','Installed','Array','Update','Row','Tensor','Inactive','Kernel','Successor','Absorption','PointFactor','CircleFactor','LineFactor','DoubleFactor','Coefficient']
for label in labels:
 m='R1Z.PV_RunJoin_Weight'+label+'46'
 source=R/'docs/research/v8-r0-zk-20261009/lean'/(m.replace('.','/')+'.lean');sha=hashlib.sha256(source.read_bytes()).hexdigest()
 records=[r for p in E.glob('modules-*.json') for r in json.loads(p.read_text()) if r['module']==m and r['source_sha256']==sha]
 if any(r['accepted'] for r in records):
  print('REUSE',m,flush=True);continue
 assert not records,('unchanged failed source',m,sha)
 assert a<61497,'audit reserve'
 r=subprocess.run([sys.executable,str(T/'focused.py'),str(a),m])
 if r.returncode:raise SystemExit(r.returncode)
 a+=1
print('NEXT ID',a,flush=True)
