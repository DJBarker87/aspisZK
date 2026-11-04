"""One bounded raw-audit group per charged attempt; no unchanged retry."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent;groups=json.loads((E/'NGE_AUDIT_ROOTS.json').read_text())['groups']
lo=int(sys.argv[1]) if len(sys.argv)>1 else 0
for i in range(lo,len(groups)):
 a=f'NGE_L{39+i:03}';mode='proof'+str(i)
 r=subprocess.run([sys.executable,str(E/'NGE_run.py'),a,'audit',mode],capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 print(a,mode,'roots',len(groups[i]),'exit',r.returncode,flush=True)
 if r.returncode:print(r.stdout[-2500:]+r.stderr,flush=True);sys.exit(r.returncode)
