from pathlib import Path
import json,subprocess,sys,os
E=Path(__file__).resolve().parent;p=json.loads((E/'NFS_RETARGET_PROVENANCE.json').read_text())
for i,_ in enumerate(p['groups']):
 a=f'NFS_L{43+i:03}';m=f'NFS_AccumPart{i:02}'
 r=subprocess.run([sys.executable,str(E/'NFS_run.py'),a,'lean',m],env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'},capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr);print(a,m,r.returncode,r.stdout[-500:],flush=True)
 if r.returncode:sys.exit(r.returncode)
