from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[('NGC_K009','kani','NGC_digest::digest_forward',True,True),('NGC_K010','kani','NGC_digest::digest_copy_positive',False,True),('NGC_K011','kani','NGC_digest::digest_copy_negative',False,True),('NGC_L006','lean','NGC_COMBINED_IMPORT',False,False),('NGC_L007','lean','NGC_WALKER',False,False),('NGC_L008','lean','NGC_MemoryLimit',False,False),('NGC_L009','lean','NGC_Driver',False,False),('NGC_L010','linkaudit','NGC_Driver',False,False),('NGC_L011','auditbin','fixtures',False,False),('NGC_L012','auditbin','proof0',False,False),('NGC_L013','auditbin','scan',False,False)]
for a,kind,target,invert,program in jobs:
 env=dict(os.environ)
 if invert:env['NGC_INVERT']='1'
 if program:env['NGC_PROGRAM']='1'
 with (E/(a+'-local.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGC_run.py'),a,kind,target],env=env,stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode!=(1 if invert or target.endswith('negative')else 0):break
