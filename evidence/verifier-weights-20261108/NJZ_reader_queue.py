from pathlib import Path
import os,subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(18,'default_return',False),(19,'default_return',True),(20,'raw4_checkpoint',False),(21,'raw4_checkpoint',True),(22,'raw16_checkpoint',False),(23,'raw16_checkpoint',True),(24,'raw32_checkpoint',False),(25,'raw32_checkpoint',True)]
for n,name,bad in jobs:
 a=f'NJZ_K{n:03d}';env=dict(os.environ)
 if bad:env['NJZ_INVERT']='1'
 with (E/(a+'-summary.log')).open('w') as out:r=subprocess.run([sys.executable,str(E/'NJZ_run.py'),a,'kani','verifier::NJZ_native::'+name],env=env,stdout=out,stderr=subprocess.STDOUT)
 print(a, 'control' if bad else 'positive','exit',r.returncode,flush=True)
 # Unexpected result or any timeout stops the queue; do not rerun the shape.
 receipt=E/a/'stdout.log'
 if (r.returncode==0)==bad or not receipt.exists() or 'timed out' in receipt.read_text():sys.exit(1)
