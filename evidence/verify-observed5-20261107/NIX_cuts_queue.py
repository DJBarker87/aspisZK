from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
for a in ["NIX_L063","NIX_L064","NIX_L065"]:
 with (E/(a+"-client.log")).open("w") as f:r=subprocess.run(["python3",str(E/"NIX_run.py"),a],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:break
