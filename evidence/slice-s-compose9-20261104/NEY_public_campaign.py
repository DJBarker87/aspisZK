"""Root forwarding/Box fields after terminal return decomposition."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[('terminal',0,'argument','NEY_K053')]+[('public',slot,mode,f'NEY_K{54+slot*2+(mode=="value"):03}') for slot in range(26) for mode in ['positive','value']]+[('public',0,'allocation','NEY_K106'),('public',1,'reply','NEY_K107')]
for family,slot,mode,a in jobs:
 if (E/a/'receipt.json').exists():continue
 subprocess.run([sys.executable,str(E/('NEY_prepare_'+family+'.py')),str(slot),mode],check=True)
 current='NEY_TERMINAL_CURRENT.json' if family=='terminal' else 'NEY_PUBLIC_CURRENT.json'
 (E/(a+'-shape.json')).write_bytes((E/current).read_bytes())
 runner='NEY_kani_run.py' if family=='terminal' else 'NEY_program_kani_run.py'
 harness='pool_v1::pair_forest_terminal::NEY_terminal::terminal' if family=='terminal' else 'r1_pool_adapter::NEY_public::public'
 subprocess.run([sys.executable,str(E/runner),a,'kani',harness])
 assert (E/a/'receipt.json').exists(),'Missing receipt: recover read-only'
 r=json.loads((E/a/'receipt.json').read_text());print(json.dumps(dict(attempt=a,family=family,slot=slot,mode=mode,exit=r['exit_status'])),flush=True)
 if r['exit_status'] not in [0,1,124]:raise SystemExit('Non-verdict: inspect before next launch')
