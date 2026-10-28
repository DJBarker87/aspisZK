from pathlib import Path
import sys,json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-own-20261028'
start=int(sys.argv[1]);names=sys.argv[2:]
for n,name in enumerate(names,start):
 assert n<61797
 p=subprocess.run([sys.executable,str(Path(__file__).with_name('lean.py')),str(n),'R1Z/PV_OWN_'+name],capture_output=True,text=True)
 (E/f'{n}-driver.log').write_text(p.stdout+p.stderr)
 print(n,name,p.returncode,flush=True)
 if p.returncode:print((p.stdout+p.stderr)[-4500:],flush=True);sys.exit(p.returncode)
