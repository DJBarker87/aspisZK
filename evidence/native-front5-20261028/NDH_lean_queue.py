from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
jobs=[(18,'NDH_Decode8'),(19,'NDH_Qm31Result'),(20,'NDH_Cmr'),(21,'NDH_RegistrySlots'),(22,'NDH_RegistryAssociation'),(23,'NDH_PolicySlot'),(24,'NDH_FromFnTotal')]
for n,target in jobs:
 a=f'NDH_L{n:03}'
 with (E/(a+'-queue.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NDH_run.py'),a,'lean',target],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise SystemExit('wrapper failure; inspect before continuing')
