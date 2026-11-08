from pathlib import Path
import subprocess,sys
E=Path('evidence/pv-lib-20261107/lane-A/session8')
for a,fid in [(47457,608),(47458,661),(47459,486),(47460,584)]:
 m='PV_LIB_A_TypedBody'+str(fid)
 r=subprocess.run([sys.executable,'evidence/pv-lib-20261107/lane-A/compile-s8.py',str(a),m])
 if r.returncode:sys.exit(r.returncode)
 paths=[str(p)for p in E.iterdir() if '-'+str(a)+'.' in p.name]
 subprocess.run(['git','add',*paths],check=True)
 subprocess.run(['git','commit','-m','Bind specialized emitted destructor body '+str(fid),'--','lean/'+m+'.lean',*paths],check=True)
