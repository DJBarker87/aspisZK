from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for a,target in [('NIX_L009','NIX_DecodeFinish'),('NIX_L010','NIX_RecordAtOrigin'),('NIX_L011','NIX_PrefixFrames'),('NIX_L012','NIX_InspectCircle')]:
 subprocess.run(['python3',str(E/'NIX_config.py'),a,'lean',target],check=True)
 with (E/(a+'-client.log')).open('w') as log:r=subprocess.run(['python3',str(E/'NIX_run.py'),a],stdout=log,stderr=subprocess.STDOUT)
 print(a,'exit',r.returncode,flush=True)
