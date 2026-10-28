from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
jobs=[(2,'NDH_kmx::KMX_checks::KMX_slice_wrong',None),(3,'fast_domain::NDH_native::table_contract',None),(4,'fast_domain::NDH_native::table_contract','table'),(5,'compact::NDH_native::slot_contract',None),(6,'compact::NDH_native::slot_contract','slot'),(7,'NDH_public::fibre_get',None),(8,'NDH_public::fibre_wrong',None),(9,'NDH_public::fibre_new',None),(10,'NDH_public::fibre_new_wrong',None)]
for i,target,invert in jobs:
 env=dict(os.environ)
 if invert:env['NDH_INVERT']=invert
 a=f'NDH_K{i:03}'
 with (E/(a+'-queue.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NDH_run.py'),a,'kani',target],env=env,stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise SystemExit('wrapper failure; inspect before continuing')
