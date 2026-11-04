from pathlib import Path
import subprocess,sys,os
E=Path(__file__).resolve().parent
for i,kind,target in [(85,'lean','NFS_ProofDriver'),(86,'lean','NFS_Driver'),(87,'auditbatch','final')]:
 a=f'NFS_L{i:03}'
 r=subprocess.run([sys.executable,str(E/'NFS_run.py'),a,kind,target],env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'},capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr);print(a,target,r.returncode,r.stdout[-1500:],flush=True)
 if r.returncode:sys.exit(r.returncode)
