from pathlib import Path
import sys,subprocess,time,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2f-20261029'
for spec in sys.argv[1:]:
 n,m=spec.split(':',1)
 for retry in range(11):
  with (E/(n+'-driver.log')).open('a') as log:
   r=subprocess.run([sys.executable,str(Path(__file__).with_name('lean.py')),n,m],stdout=log,stderr=subprocess.STDOUT)
  if r.returncode==78 and retry<10:
   print('admission hold '+n+'; full180s cooldown',flush=True);time.sleep(180);continue
  break
 print(n,m,'exit',r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
