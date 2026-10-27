from pathlib import Path
import json,subprocess,sys
P=Path(__file__).resolve().parent
rows=json.loads((P/'JHc_COMPRESSION.json').read_text())
# Cert0_00 was independently preflighted at003; Review70 remains reserved.
selected=rows[1:-1]
assert len(selected)==66
for n,r in enumerate(selected,4):
 assert n<70
 print(f"START {n:03} {r['module']}",flush=True)
 result=subprocess.run([sys.executable,str(P/'JHc_compile.py'),str(n),r['module']],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (P/f'JHc29_{n:03}-driver.log').write_text(result.stdout)
 print(f"END {n:03} exit={result.returncode}",flush=True)
 if result.returncode:sys.exit(result.returncode)
