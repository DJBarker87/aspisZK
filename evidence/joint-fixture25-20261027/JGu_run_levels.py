from pathlib import Path
import subprocess,json,sys
P=Path(__file__).resolve().parent
n=int(sys.argv[1]); mods=sys.argv[2:]
for m in mods:
 r=subprocess.run([sys.executable,str(P/'JGu_compile.py'),str(n),m])
 if r.returncode:sys.exit(r.returncode)
 receipt=json.loads((P/f'JGu25_{n:03}/receipt.json').read_text())
 print(m,receipt['exit_status'],receipt['wall_seconds'],receipt['peak_rss_kib'],flush=True)
 n+=1
