from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
jobs=[(30,'shape_contract',False,0),(31,'shape_contract',True,1),(32,'shape_weak_contract',False,0),(33,'shape_real',False,0),(34,'shape_unimplied',False,1),(35,'shape_frame',False,1),(36,'copy_positive',False,0),(37,'copy_negative',False,1)]
for k,target,invert,expected in jobs:
 a=f'NGH_K{k:03}';env=dict(os.environ,NGH_CORE='1',NGH_FOR='1',NGH_LOOP_DEBUG='1')
 if invert:env['NGH_INVERT']='1'
 r=subprocess.run(['python3',str(E/'NGH_run.py'),a,'kani','field::NGH_contracts::'+target],env=env,capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr);p=E/a/'receipt.json'
 if not p.exists():raise RuntimeError(r.stdout+r.stderr)
 x=json.loads(p.read_text());print(a,target,x['exit_status'],x['wall_seconds'],flush=True)
 if x['exit_status']!=expected:raise RuntimeError('Unexpected fidelity verdict; inspect before any dependence')
 if 'CBMC timed out'in(E/a/'stdout.log').read_text():raise RuntimeError('No credit for timeout')
