from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
with(E/'NGC_L031-local.log').open('w')as f:r=subprocess.run(['python3',str(E/'NGC_run.py'),'NGC_L031','lean','NGC_WriterDomain'],stdout=f,stderr=subprocess.STDOUT)
print('NGC_L031',r.returncode,flush=True)
for k,name,invert in [(20,'heap_schedule',False),(21,'heap_schedule',True),(22,'heap_u8',False),(23,'heap_u8',True),(24,'heap_raw',False),(25,'heap_raw',True),(26,'heap_wide',False),(27,'heap_wide',True),(28,'heap_payload_positive',False),(29,'heap_payload_negative',False)]:
 a=f'NGC_K{k:03}';env=dict(os.environ)
 if invert:env['NGC_INVERT']='1'
 with(E/(a+'-local.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGC_run.py'),a,'kani','verifier::NGC_windows::'+name],env=env,stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode!=(1 if invert or name.endswith('negative')else 0):break
