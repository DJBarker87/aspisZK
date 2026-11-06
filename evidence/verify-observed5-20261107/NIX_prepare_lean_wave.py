from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
for a,mod in [('NIX_L073','NIX_ProducerInstall'),('NIX_L074','NIX_ActiveFrames'),('NIX_L075','NIX_BASE_IMPORT'),('NIX_L076',None),('NIX_L077','NIX_DispatchRun')]:
 if mod:subprocess.run(['python3',str(E/'NIX_config.py'),a,'lean',mod],check=True)
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NIX_run.py'),a],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode and a=='NIX_L076':break
