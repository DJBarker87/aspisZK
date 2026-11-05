from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
for a in ["NIX_L071","NIX_L072","NIX_K069"]:
 with (E/(a+"-client.log")).open("w") as f:r=subprocess.run(["python3",str(E/"NIX_run.py"),a],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)

