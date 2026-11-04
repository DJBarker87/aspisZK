from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
r=subprocess.run(['python3',str(E/'NGC_digest_expand_prepare.py')]);assert r.returncode==0
jobs=[(82,'NGC_digest::digest_forward',False,True),(83,'NGC_digest::digest_forward',True,True),(84,'NGC_digest::digest_copy_positive',False,True),(85,'NGC_digest::digest_copy_negative',False,True)]
def run(k,target,invert,program):
 a=f'NGC_K{k:03}';env=dict(os.environ)
 if invert:env['NGC_INVERT']='1'
 if program:env['NGC_PROGRAM']='1'
 with(E/(a+'-local.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGC_run.py'),a,'kani',target],env=env,stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 assert r.returncode==(1 if invert or target.endswith('negative')else 0),a
for j in jobs:run(*j)
r=subprocess.run(['python3',str(E/'NGC_heap_reserve_prepare.py')]);assert r.returncode==0
for k,typ in [(86,'u8'),(88,'q'),(90,'raw'),(92,'wide')]:
 for invert in [False,True]:run(k+int(invert),'verifier::NGC_windows::reserve_prefix_'+typ,invert,False)
for invert in [False,True]:run(94+int(invert),'verifier::NGC_windows::new_allocation_error',invert,False)
