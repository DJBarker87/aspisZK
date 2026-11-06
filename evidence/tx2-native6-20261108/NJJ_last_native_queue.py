from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[]
for start,name in [(66,'resume_allocation_site'),(70,'pending_allocation_site')]:
 for d,cfg in enumerate([None,'NJJ_INVERT','NJJ_BAD_ERROR','NJJ_BAD_ALLOC']):jobs.append((start+d,'verifier::NJJ_parent::'+name,cfg, cfg is not None))
for start,name in [(74,'pending_stop'),(76,'finish_stop'),(78,'weights_stop')]:
 jobs.extend([(start,'verifier::NJJ_parent::'+name,None,False),(start+1,'verifier::NJJ_parent::'+name,'NJJ_INVERT',True)])
jobs.append((80,'KMX_ptr_wrong',None,True))
for n,name,cfg,fail in jobs:
 env=os.environ.copy()
 if cfg:env[cfg]='1'
 a=f'NJJ_K{n:03d}';r=subprocess.run(['python3',str(E/'NJJ_run.py'),a,'kani',name],env=env)
 assert (r.returncode==0)==(not fail),(a,r.returncode)
 log=(E/a/'stdout.log').read_text();assert 'timed out' not in log
 if fail:assert 'VERIFICATION:- FAILED' in log
