from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for n,t in [(62,'NDH_RegistryPrimitives'),(63,'NDH_NativeDomains'),(64,'NDH_RegistryActiveSlots')]:
 a=f'NDH_L{n:03}'
 with (E/(a+'-queue.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NDH_run.py'),a,'lean',t],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise SystemExit('wrapper failure')
