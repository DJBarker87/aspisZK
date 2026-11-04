from pathlib import Path
import sys,subprocess,json
E=Path(__file__).resolve().parent
for s,shape in enumerate(['add','asset','requested','joined']):
 for off,mode in enumerate(['positive','negative']):
  a=f'NFD_K{70+2*s+off:03}';subprocess.run([sys.executable,str(E/'NFD_prepare_guard.py'),shape,mode],check=True)
  (E/(a+'-shape.json')).write_bytes((E/'NFD_GUARD_CURRENT.json').read_bytes())
  subprocess.run([sys.executable,str(E/'NFD_program_kani_run.py'),a,'kani','r1_pool_adapter::NFD_guard::guard_cut'])
  r=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text();print(json.dumps(dict(attempt=a,shape=shape,exit=r['exit_status'])),flush=True)
  if r['exit_status'] in [124,137] or 'timed out' in log.lower():raise SystemExit('family stopped for review')
  assert r['exit_status']==(0 if mode=='positive' else 1)
  assert mode=='positive' or 'Failed Checks:' in log
