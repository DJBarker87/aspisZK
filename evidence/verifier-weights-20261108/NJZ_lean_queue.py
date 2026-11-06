from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for n,name in [(21,'NJZ_Weights'),(22,'NJZ_EmptyTree'),(23,'NJZ_TreeParent'),(24,'NJZ_CodecProjection')]:
 a=f'NJZ_L{n:03d}'
 with (E/(a+'-summary.log')).open('w') as out:r=subprocess.run([sys.executable,str(E/'NJZ_run.py'),a,'lean',name],stdout=out,stderr=subprocess.STDOUT)
 print(a,name,'exit',r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
