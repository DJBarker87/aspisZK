from pathlib import Path
import subprocess,sys,os
E=Path(__file__).resolve().parent
for i,target in [(69,'NFS_DotTrace'),(70,'NFS_QueryValuesPacket')]:
 a=f'NFS_L{i:03}'
 r=subprocess.run([sys.executable,str(E/'NFS_run.py'),a,'lean',target],env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'},capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr);print(a,target,r.returncode,r.stdout[-2500:],flush=True)
 if r.returncode:sys.exit(r.returncode)
