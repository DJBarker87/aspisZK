from pathlib import Path
import sys,subprocess,json
E=Path(__file__).resolve().parent
jobs=[(38+2*slot+off,slot,mode) for slot in range(15) for off,mode in enumerate(['positive','negative'])]+[(68,0,'wrong_allocation')]
for n,slot,mode in jobs:
 a=f'NFD_K{n:03}'
 if (E/a/'receipt.json').exists():continue
 subprocess.run([sys.executable,str(E/'NFD_prepare_reconstruct.py'),'common_actual',mode,str(slot)],check=True)
 (E/(a+'-shape.json')).write_bytes((E/'NFD_RECONSTRUCT_CURRENT.json').read_bytes())
 subprocess.run([sys.executable,str(E/'NFD_program_kani_run.py'),a,'kani','r1_pool_adapter::NFD_reconstruct::reconstruction_slice'])
 rc=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text();print(json.dumps(dict(attempt=a,slot=slot,mode=mode,exit=rc['exit_status'])),flush=True)
 if rc['exit_status'] in [124,137] or 'timed out' in log.lower():raise SystemExit('family stopped for review; no later checks submitted')
 assert rc['exit_status']==(0 if mode=='positive' else 1)
 assert mode=='positive' or 'Failed Checks:' in log
