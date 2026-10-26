from pathlib import Path
import sys,subprocess,json
P=Path(__file__).resolve().parent
n=int(sys.argv[1])
for mod in sys.argv[2:]:
 assert n<=100
 with (P/f'JFu12_{n:03}-driver.log').open('w') as f:r=subprocess.run([sys.executable,str(P/'JFu_compile.py'),str(n),mod],stdout=f,stderr=subprocess.STDOUT)
 print(n,mod,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
 n+=1
