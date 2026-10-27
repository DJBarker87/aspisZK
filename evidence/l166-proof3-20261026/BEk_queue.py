"""Sequential task list using the existing capped launcher; no infrastructure changes."""
from pathlib import Path
import subprocess,sys,json
P=Path(__file__).resolve().parent
for entry in sys.argv[1:]:
 n,mod=entry.split(':',1)
 print(n,mod,flush=True)
 with (P/f'BEk_{int(n):03}-driver.log').open('w') as log:
  result=subprocess.run([sys.executable,str(P/'BEk_compile.py'),n,mod],stdout=log,stderr=subprocess.STDOUT)
 receipt=P/f'BEk_{int(n):03}'/'receipt.json'
 if receipt.exists():
  r=json.loads(receipt.read_text());print({k:r[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib']},flush=True)
 if result.returncode:sys.exit(result.returncode)
