from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(127,'limbs','positive'),(128,'limbs','value'),(129,'tag','positive'),(130,'tag','value'),(131,'bytes','positive'),(132,'bytes','value'),(133,'bytes','frame')]
for n,shape,mode in jobs:
 a=f'NFD_K{n:03}'
 subprocess.run([sys.executable,str(E/'NFD_prepare_raw.py'),shape,mode],check=True)
 (E/(a+'-shape.json')).write_bytes((E/'NFD_RAW_CURRENT.json').read_bytes())
 subprocess.run([sys.executable,str(E/'NFD_program_kani_run.py'),a,'kani','r1_pool_adapter::NFD_raw::raw'])
 r=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 print(json.dumps(dict(attempt=a,shape=shape,mode=mode,exit=r['exit_status'])),flush=True)
 if r['exit_status'] in [124,137] or 'timed out' in log.lower():raise SystemExit('family stopped for review')
 assert r['exit_status']==(0 if mode=='positive' else 1)
 assert mode=='positive' or 'Failed Checks:' in log
