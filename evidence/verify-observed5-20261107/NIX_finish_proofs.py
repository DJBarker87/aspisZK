from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
for a,mod in [('NIX_L084','NIX_DispatchRun'),('NIX_L086','NIX_CertificateFrames')]:
 if mod:subprocess.run(['python3',str(E/'NIX_config.py'),a,'lean',mod],check=True)
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NIX_run.py'),a],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode and a=='NIX_L076':break
