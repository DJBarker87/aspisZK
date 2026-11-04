from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for n,t in [(10,'NGN_RowArithmetic'),(11,'NGN_EmittedEq'),(12,'NGN_ScalarDomains')]:
 a=f'NGN_L{n:03d}';r=subprocess.run([sys.executable,str(E/'NGN_run.py'),a,'lean',t],text=True,capture_output=True);(E/(a+'-client.log')).write_text(r.stdout+r.stderr);print(a,r.returncode,r.stdout[-900:],flush=True)
 if r.returncode:break
