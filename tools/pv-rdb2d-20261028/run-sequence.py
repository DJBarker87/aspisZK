from pathlib import Path
import subprocess,sys,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2d-20261028'
for arg in sys.argv[1:]:
 n,m=arg.split(':',1)
 for retry in range(11):
  with (E/f'{n}-driver.log').open('a')as o:r=subprocess.run([sys.executable,str(R/'tools/pv-rdb2d-20261028/lean.py'),n,'R1Z/PV_RDB2D_'+m],stdout=o,stderr=subprocess.STDOUT)
  if r.returncode==78 and retry<10:print('refused',n,'180s cooldown',flush=True);time.sleep(180);continue
  break
 print(n,m,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
