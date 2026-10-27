"""Sequential proof orchestration, using the unchanged capped host launcher."""
from pathlib import Path
import subprocess,sys,json
P=Path(__file__).resolve().parent
n=int(sys.argv[1]);mods=sys.argv[2:]
for m in mods:
 assert n<=100
 print(f'BEGIN {n:03} {m}',flush=True)
 r=subprocess.run([sys.executable,str(P/'JFz_TX2_compile.py'),str(n),m],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (P/f'JFz_TX2_{n:03}-driver.log').write_text(r.stdout)
 print(r.stdout[-1200:],flush=True)
 print(f'END {n:03} exit={r.returncode}',flush=True)
 if r.returncode:sys.exit(r.returncode)
 n+=1
