from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for n,target in [(43,'NJZ_CodecProjection'),(44,'NJZ_CodecSemantics')]:
 a=f'NJZ_L{n:03d}'
 with (E/(a+'-summary.log')).open('w') as out:r=subprocess.run([sys.executable,str(E/'NJZ_run.py'),a,'lean',target],stdout=out,stderr=subprocess.STDOUT)
 print(a,target,'exit',r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
