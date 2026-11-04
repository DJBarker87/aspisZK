"""Remaining independently scoped slice checks; never retry a timed-out input."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[]
for n,mode in enumerate(['positive','value','argument'],108):jobs.append((n,'binding',[mode],'NEY_BINDING_CURRENT.json','pool_v1::pair_forest_terminal::NEY_binding::binding',False))
for slot in range(9):
 for offset,mode in enumerate(['positive','value']):jobs.append((111+slot*2+offset,'result_parent',[str(slot),mode],'NEY_RESULT_PARENT_CURRENT.json','pool_v1::pair_forest_terminal::NEY_result_parent::result_parent',False))
for n,mode in enumerate(['positive','byte','order','argument'],129):jobs.append((n,'emit_parent',[mode],'NEY_EMIT_PARENT_CURRENT.json','r1_pool_adapter::NEY_emit_parent::emit_parent',True))
for offset,shape in enumerate(['magic','zero']):
 for control,mode in enumerate(['positive','value']):jobs.append((133+offset*2+control,'request_comparison',[shape,mode],'NEY_REQUEST_COMPARISON_CURRENT.json','pool_v1::pair_forest_terminal::NEY_request_comparison::request_comparison',False))
for slot in range(5):
 for offset,mode in enumerate(['positive','negative']):jobs.append((137+slot*2+offset,'common_field',['common',mode,str(slot)],'NEY_RECONSTRUCT_CURRENT.json','r1_pool_adapter::NEY_reconstruct::reconstruction_slice',True))
for offset,shape in enumerate(['limbs','tag']):
 for control,mode in enumerate(['positive','value']):jobs.append((147+offset*2+control,'scalar',[shape,mode],'NEY_SCALAR_CURRENT.json','r1_pool_adapter::NEY_scalar::scalar',True))
assert [j[0] for j in jobs]==list(range(108,151))
for n,generator,args,current,harness,program in jobs:
 a=f'NEY_K{n:03}'
 if (E/a/'receipt.json').exists():continue
 subprocess.run([sys.executable,str(E/('NEY_prepare_'+generator+'.py')),*args],check=True)
 (E/(a+'-shape.json')).write_bytes((E/current).read_bytes())
 r=subprocess.run([sys.executable,str(E/('NEY_program_kani_run.py' if program else 'NEY_kani_run.py')),a,'kani',harness])
 assert (E/a/'receipt.json').exists(),'Missing receipt; recover read-only'
 rc=json.loads((E/a/'receipt.json').read_text());print(json.dumps(dict(attempt=a,shape=generator,arguments=args,exit=rc['exit_status'])),flush=True)
 if rc['exit_status'] not in [0,1,124]:raise SystemExit('Non-verdict: inspect before another launch')
 log=(E/a/'stdout.log').read_text()
 if not any(marker in log for marker in ['VERIFICATION:- SUCCESSFUL','VERIFICATION:- FAILED','timed out']) and rc['exit_status']!=124:raise SystemExit('Compile/gate failure: repair private inputs before dependent launch')
