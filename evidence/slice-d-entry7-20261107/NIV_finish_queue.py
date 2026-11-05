import sys,subprocess
from pathlib import Path
from NIV_formal import run,E
for a,m in [('NIV_L035','NIV_RawBoundary'),('NIV_L036','NIV_AuthPrefixes')]:
 r=run(a,'lean',m)
 if r['exit_status']:sys.exit(r['exit_status'])
for script,args in [('NIV_prepare_audit.py',[]),('NIV_audit_stage.py',[]),('NIV_make_sdk.py',['remaining']),('NIV_packet_queue.py',['sdk'])]:
 r=subprocess.run([sys.executable,str(E/script),*args])
 if r.returncode:sys.exit(r.returncode)
print('NIV_FINISH_QUEUE_PASS',flush=True)
