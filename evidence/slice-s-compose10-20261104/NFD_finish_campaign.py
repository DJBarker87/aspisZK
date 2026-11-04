from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(91+2*s+off,'finish',m,s) for s in range(9) for off,m in enumerate(['positive','negative'])]+[(109,'finish','wrong_common',0),(110,'finish','wrong_reply',0)]
for n,shape,mode,slot in jobs:
 a=f'NFD_K{n:03}'
 subprocess.run([sys.executable,str(E/'NFD_prepare_reconstruct.py'),shape,mode,str(slot)],check=True)
 (E/(a+'-shape.json')).write_bytes((E/'NFD_RECONSTRUCT_CURRENT.json').read_bytes())
 subprocess.run([sys.executable,str(E/'NFD_program_kani_run.py'),a,'kani','r1_pool_adapter::NFD_reconstruct::reconstruction_slice'])
 r=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 print(json.dumps(dict(attempt=a,mode=mode,slot=slot,exit=r['exit_status'])),flush=True)
 if r['exit_status'] in [124,137] or 'timed out' in log.lower():raise SystemExit('family stopped for review')
 assert r['exit_status']==(0 if mode=='positive' else 1)
 assert mode=='positive' or 'Failed Checks:' in log
