from pathlib import Path
import subprocess,sys,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2d-20261028';D='/home/dombarker/project-offloads/codex-pv-rdb2c-20261028'
for retry in range(11):
 with (E/'sparse-native-driver.log').open('a')as o:r=subprocess.run([sys.executable,str(R/'tools/pv-rdb2d-20261028/scope.py'),'rdb2d-sparse-native','optimized layout probe across eleven widths and two actual abort prefixes; finite validation','python3',D+'/rdb2d-sparse-native.py'],stdout=o,stderr=subprocess.STDOUT)
 if r.returncode==78 and retry<10:print('native admission hold;180s cooldown',flush=True);time.sleep(180);continue
 break
if r.returncode:sys.exit(r.returncode)
r=subprocess.run([sys.executable,str(R/'tools/pv-rdb2d-20261028/run-sequence.py'),'61097:StatementAudit','61098:AxiomsAudit'])
sys.exit(r.returncode)
