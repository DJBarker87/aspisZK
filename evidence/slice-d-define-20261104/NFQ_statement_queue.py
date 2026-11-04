from pathlib import Path
import subprocess,os,sys,json
E=Path(__file__).resolve().parent
S='pool_v1::pair_forest_semantic_terminal::NFQ_stmt::';P='state_only_poseidon::NFQ_poseidon::'
jobs=[(34,S+'variant_contract',1,True),(35,S+'copy_contract',0,False),(36,S+'copy_contract',1,True),(37,P+'limbs_contract',0,False),(38,P+'limbs_contract',1,True),(39,P+'copy_positive',0,False),(40,P+'copy_negative',1,False),(41,S+'enum_real',0,False),(42,S+'enum_unimplied',1,False),(43,S+'enum_frame',1,False),(44,P+'array_real',0,False),(45,P+'array_unimplied',1,False),(46,P+'array_frame',1,False)]
for i,target,expected,invert in jobs:
 a=f'NFQ_K{i:03}';env=dict(os.environ,NFQ_STATEMENT='1')
 if invert:env['NFQ_INVERT']='1'
 r=subprocess.run([sys.executable,str(E/'NFQ_run.py'),a,'kani',target],env=env,capture_output=True,text=True)
 (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
 rc=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text()
 assert rc['exit_status']==expected and 'VERIFICATION:- '+('FAILED' if expected else 'SUCCESSFUL') in out,(a,'unexpected verdict',rc['exit_status'])
 print(json.dumps(dict(attempt=a,exit=rc['exit_status'],wall=rc['wall_seconds'])),flush=True)
