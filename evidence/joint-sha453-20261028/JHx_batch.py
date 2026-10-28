"""Sequential proof task list; stop immediately on any nonzero compile."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
manifest=json.loads((E/'JHx_GENERATOR_CHECK.json').read_text())
start=int(sys.argv[1]);mods=sys.argv[2:]
for n,mod in enumerate(mods,start):
 attempt=f'JHx_{n:03}'
 print(attempt,mod,flush=True)
 with (E/(attempt+'-controller.log')).open('w') as out:
  r=subprocess.run([sys.executable,str(E/'JHx_compile.py'),'preflight',attempt,mod],stdout=out,stderr=subprocess.STDOUT)
 if r.returncode:raise SystemExit(f'Stopped at {attempt}, exit{r.returncode}')
 x=json.loads((E/attempt/'receipt.json').read_text());print(json.dumps({k:x[k] for k in ['exit_status','wall_seconds','peak_rss_kib','swaps']}),flush=True)
