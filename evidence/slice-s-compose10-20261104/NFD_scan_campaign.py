from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[('length','positive',0),('length','negative',0),('tag','positive',0),('tag','negative',0)]+[('prefix',m,s) for s in range(3) for m in ['positive','negative']]+[('prefix','allocation',0),('prefix','reply',0),('finish','positive',0),('finish','negative',0),('equality','positive',0),('equality','negative',0),('equality','argument',0)]
assert len(jobs)==17
for n,(shape,mode,slot) in enumerate(jobs,134):
 a=f'NFD_K{n:03}'
 subprocess.run([sys.executable,str(E/'NFD_prepare_scan.py'),shape,mode,str(slot)],check=True)
 (E/(a+'-shape.json')).write_bytes((E/'NFD_SCAN_CURRENT.json').read_bytes())
 subprocess.run([sys.executable,str(E/'NFD_program_kani_run.py'),a,'kani','r1_pool_adapter::NFD_scan::scan_cut'])
 r=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 print(json.dumps(dict(attempt=a,shape=shape,mode=mode,slot=slot,exit=r['exit_status'])),flush=True)
 if r['exit_status'] in [124,137] or 'timed out' in log.lower():raise SystemExit('family stopped for review')
 assert r['exit_status']==(0 if mode=='positive' else 1)
 assert mode=='positive' or 'Failed Checks:' in log
