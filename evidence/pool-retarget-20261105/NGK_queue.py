from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
x=json.loads((E/'NGK_PROVENANCE.json').read_text())
for i,n in enumerate(x['order'][32:],33):
 a=f'NGK_L{i:03}';log=E/(a+'-client.log')
 r=subprocess.run([sys.executable,str(E/'NGK_run.py'),a,'lean','NGK_'+n],capture_output=True,text=True)
 log.write_text(r.stdout+r.stderr);print(a,n,'exit',r.returncode,flush=True)
 if r.returncode:print((r.stdout+r.stderr)[-2800:],flush=True);sys.exit(r.returncode)
