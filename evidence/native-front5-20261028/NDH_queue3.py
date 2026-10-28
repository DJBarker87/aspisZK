from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[];i=33
for t,meths in [('verifierregistryv1',['is_immutable','is_paused']),('verifierregistryv2',['is_immutable','is_paused']),('verifierregistryentryv1',['has_no_retirement_slot']),('verifierregistryentryv2',['has_no_retirement_slot'])]:
 for meth in meths:
  jobs.extend([(i,'NDH_public::'+t+'_'+meth,None),(i+1,'NDH_public::'+t+'_'+meth,meth)]);i+=2
jobs += [(45,'compact::NDH_native::slot_step',None),(46,'compact::NDH_native::slot_step','slot_step')]
for i,target,invert in jobs:
 env=dict(os.environ)
 if invert:env['NDH_INVERT']=invert
 a=f'NDH_K{i:03}'
 with (E/(a+'-queue.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NDH_run.py'),a,'kani',target],env=env,stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise SystemExit('wrapper failure; inspect before continuing')
