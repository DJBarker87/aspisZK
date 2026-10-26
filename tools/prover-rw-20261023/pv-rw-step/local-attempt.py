"""One tiny cached Std-only local compile with immutable input and receipt."""
from pathlib import Path
import subprocess,sys
r=Path(__file__).resolve().parents[3];a=int(sys.argv[1]);m=sys.argv[2];t=Path(__file__).parent
subprocess.run([sys.executable,str(t/'local-input.py'),str(a),m],check=True)
p=r/'docs/research/v8-r0-zk-20261009/lean';cache=Path('/private/tmp/pv-rw-step-local-20261026')
log=r/f'evidence/pv-rw-step-20261026/local-{a}.log'
with log.open('w') as out:
 result=subprocess.run(['/usr/bin/time','-l','env','LEAN_PATH='+str(cache),'lake','env','lean','-M7000','-R',str(p),'-o',str(cache/'R1Z'/(m+'.olean')),str(p/'R1Z'/(m+'.lean'))],cwd=r/'docs/research/100bit-spend-path-20261013/evidence/s2d-20261023',stdout=out,stderr=subprocess.STDOUT)
subprocess.run([sys.executable,str(t/'collect-local.py'),str(a),m,str(result.returncode)],check=True)
print(log.read_text().split(' real')[0]);raise SystemExit(result.returncode)
