from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,m in [(29,'NFW_StoredLayout'),(30,'NFW_StoredWindows'),(31,'NFW_QueryEntry')]:
 r=subprocess.run([sys.executable,str(E/'NFW_run.py'),f'NFW_L{i:03}','lean',m],capture_output=True,text=True)
 (E/f'NFW_L{i:03}-queue.log').write_text(r.stdout+r.stderr)
 print(i,m,r.returncode,r.stdout[-2200:],flush=True)
 if r.returncode:sys.exit(r.returncode)
