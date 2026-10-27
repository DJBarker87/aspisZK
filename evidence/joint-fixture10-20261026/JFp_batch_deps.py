from pathlib import Path
import subprocess,sys,json
P=Path(__file__).resolve().parent
for n,mod in enumerate(json.loads((P/'JFp_DEPENDENCY_ORDER.json').read_text()),43):
 with (P/f'JFp_{n:03}-driver.log').open('w') as out:
  r=subprocess.run([sys.executable,str(P/'JFp_compile.py'),str(n),mod],stdout=out,stderr=subprocess.STDOUT)
 print(n,mod,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
