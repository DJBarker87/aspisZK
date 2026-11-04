"""Last 13 successful slots after retained L097 failure: complete kernel-loaded certificate inventory."""
from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i in range(13):
 a=f'NGE_L{98+i:03}';target=f'NGE_CertificatePart{i:02}'
 r=subprocess.run([sys.executable,str(E/'NGE_run.py'),a,'lean',target],capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr);print(a,target,'exit',r.returncode,flush=True)
 if r.returncode:print(r.stdout[-2500:]+r.stderr,flush=True);sys.exit(r.returncode)
