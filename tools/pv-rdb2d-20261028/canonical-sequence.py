from pathlib import Path
import sys,subprocess,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2d-20261028'
for script,n,m in [('canonical-lean.py',61058,'AspisR72Sampler/Types'),('canonical-funs.py',61059,'AspisR72Sampler/Funs'),('lean.py',61060,'R1Z/PV_RDB2D_SamplerCore')]:
 for retry in range(11):
  with (E/f'{n}-driver.log').open('a') as o:r=subprocess.run([sys.executable,str(R/'tools/pv-rdb2d-20261028'/script),str(n),m],stdout=o,stderr=subprocess.STDOUT)
  if r.returncode==78 and retry<10:print('refusal',n,'cooldown180s',flush=True);time.sleep(180);continue
  break
 print(n,m,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
