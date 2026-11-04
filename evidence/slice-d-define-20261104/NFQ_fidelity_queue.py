from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[('usize_real',0),('usize_unimplied',1),('usize_frame',1),('option_real',0),('option_unimplied',1),('option_frame',1)]
for i,(target,expected) in enumerate(jobs,13):
 a=f'NFQ_K{i:03}'
 r=subprocess.run([sys.executable,str(E/'NFQ_run.py'),a,'kani','NFQ_fidelity::'+target],capture_output=True,text=True)
 (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
 rc=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text()
 assert rc['exit_status']==expected,(a,rc['exit_status'])
 assert 'VERIFICATION:- '+('FAILED' if expected else 'SUCCESSFUL') in out,(a,'not solver verdict')
 print(json.dumps(dict(attempt=a,exit=rc['exit_status'],wall=rc['wall_seconds'])),flush=True)
