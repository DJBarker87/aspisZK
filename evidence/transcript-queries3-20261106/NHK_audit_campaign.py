"""Single final raw audit, fixtures and loaded-object scan, serial and capped."""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
for n,mode in [(24,'batch0'),(25,'batch1'),(26,'fixtures'),(27,'scan')]:
 a=f'NHK_L{n:03}'
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NHK_run.py'),a,'audit',mode],stdout=f,stderr=subprocess.STDOUT)
 assert (E/a/'receipt.json').exists(),a+' missing receipt; recover only'
 receipt=json.loads((E/a/'receipt.json').read_text());print(json.dumps({k:receipt[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}),flush=True)
 if r.returncode:sys.exit(r.returncode)
