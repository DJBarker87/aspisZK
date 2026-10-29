from pathlib import Path
import subprocess,sys,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2d-20261028';D='/home/dombarker/project-offloads/codex-pv-rdb2c-20261028'
for retry in range(11):
 with (E/'fingerprint-driver.log').open('a')as o:r=subprocess.run([sys.executable,str(R/'tools/pv-rdb2d-20261028/scope.py'),'rdb2d-final-fingerprint','complete source/object cohort verification before one final replay','python3',D+'/rdb2d-fingerprint.py'],stdout=o,stderr=subprocess.STDOUT)
 if r.returncode==78 and retry<10:print('fingerprint admission hold;180s cooldown',flush=True);time.sleep(180);continue
 break
if r.returncode:sys.exit(r.returncode)
sys.exit(subprocess.run([sys.executable,str(R/'tools/pv-rdb2d-20261028/run-sequence.py'),'61099:FinalReplay']).returncode)
