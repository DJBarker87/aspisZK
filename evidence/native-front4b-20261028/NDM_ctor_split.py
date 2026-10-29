from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
a=70
for variant in ['transfer','withdrawal']:
 for mode in ['0','1']:
  for inverted in [False,True]:
   env=dict(os.environ,NDM_CTOR='1',NDM_CTOR_MODE=mode,NDM_CTOR_GROUP='0',NDM_CTOR_OBSERVE='1',NDM_ARBITRARY='1')
   if inverted:env['NDM_INVERT']='1'
   else:env.pop('NDM_INVERT',None)
   name=f'NDM_K{a:03d}';target='r1_pool_adapter::NDM_ctor::'+variant+'_contract'
   r=subprocess.run(['python3',str(E/'NDM_run.py'),name,'kani',target],env=env,capture_output=True,text=True)
   print(json.dumps(dict(attempt=name,variant=variant,mode=mode,group='scalar',inverted=inverted,runner_exit=r.returncode,output=r.stdout[-2300:],stderr=r.stderr[-1500:])),flush=True)
   if r.returncode:raise SystemExit(r.returncode)
   a+=1
   receipt=json.loads((E/name/'receipt.json').read_text())
   if not inverted and receipt['exit_status']!=0:
    print(json.dumps(dict(skip_control=variant,mode=mode,reason='positive not established')),flush=True);break
