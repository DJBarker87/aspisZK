from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,n in enumerate(['LPi_PowersStep','LPi_PowersPrefix','LPi_PowersValue','LPi_PowersSource','LPm_PowersBridge','NBQ_Powers29'],3):
 r=subprocess.run([sys.executable,str(E/'NFW_run.py'),f'NFW_L{i:03}','lean','NFW_'+n],capture_output=True,text=True)
 (E/f'NFW_L{i:03}-queue.log').write_text(r.stdout+r.stderr)
 print(n,r.returncode,r.stdout[-1200:],flush=True)
 if r.returncode:sys.exit(r.returncode)
