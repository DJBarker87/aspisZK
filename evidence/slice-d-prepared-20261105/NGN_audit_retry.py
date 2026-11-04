from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for n,t in [(33,'fixtures'),(34,'batch0'),(35,'scan')]:
 a=f'NGN_L{n:03d}';r=subprocess.run([sys.executable,str(E/'NGN_run.py'),a,'audit',t],text=True,capture_output=True);(E/(a+'-client.log')).write_text(r.stdout+r.stderr);print(a,r.returncode,r.stdout[-1400:],flush=True)
 if r.returncode:break
