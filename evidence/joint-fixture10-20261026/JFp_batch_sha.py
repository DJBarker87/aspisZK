from pathlib import Path
import subprocess,sys,json
P=Path(__file__).resolve().parent
for n,mod in [(14+j,f"JFp_SHABlock{j+1:02}") for j in range(24)]:
 with (P/f"JFp_{n:03}-driver.log").open("w") as out:
  r=subprocess.run([sys.executable,str(P/"JFp_compile.py"),str(n),mod],stdout=out,stderr=subprocess.STDOUT)
 print(n,mod,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
