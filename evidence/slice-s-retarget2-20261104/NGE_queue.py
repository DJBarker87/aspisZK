"""One own scope at a time, stop on any failed elaboration for inspection."""
from pathlib import Path
import json,sys,subprocess
E=Path(__file__).resolve().parent
p=json.loads((E/'NGE_PROVENANCE.json').read_text());start=int(sys.argv[1]);lo=int(sys.argv[2]);hi=int(sys.argv[3])
for idx,n in enumerate(p['order'][lo:hi],start):
 a=f'NGE_L{idx:03}';r=subprocess.run([sys.executable,str(E/'NGE_run.py'),a,'lean','NGE_'+n],capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr);print(a,n,r.returncode,r.stdout[-220:],flush=True)
 if r.returncode:sys.exit(r.returncode)
