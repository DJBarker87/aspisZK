from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
# Driver sources/binaries unchanged. Reuse L036's same-binary eight fixtures;
# only model objects/source-derived expected imports changed.
for n,kind,target in [(45,'lean','NJZ_COMBINED_IMPORT'),(46,'audit','all'),(47,'audit','scan')]:
 a=f'NJZ_L{n:03d}'
 with (E/(a+'-summary.log')).open('w') as out:r=subprocess.run([sys.executable,str(E/'NJZ_run.py'),a,kind,target],stdout=out,stderr=subprocess.STDOUT)
 print(a,kind,target,'exit',r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
