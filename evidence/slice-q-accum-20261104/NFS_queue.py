from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
p=json.loads((E/'NFS_RETARGET_PROVENANCE.json').read_text())
start=int(sys.argv[1]); first=int(sys.argv[2])
for i,n in enumerate(p['order'][start:],first):
 a=f'NFS_L{i:03}';m=p['owner'][n]
 r=subprocess.run([sys.executable,str(E/'NFS_run.py'),a,'lean',m],env={**__import__('os').environ,'PYTHONDONTWRITEBYTECODE':'1'},capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 print(a,m,r.returncode,r.stdout[-300:],flush=True)
 if r.returncode:sys.exit(r.returncode)
