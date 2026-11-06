from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,target in [('NIX_L067',None),('NIX_L068','NIX_ObservedCongruence'),('NIX_L069','NIX_InspectProducer')]:
 if target:subprocess.run(['python3',str(E/'NIX_config.py'),a,'lean',target],check=True)
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NIX_run.py'),a],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:break
