from pathlib import Path
import subprocess,time,sys,json
E=Path(__file__).resolve().parent
# Read-only local wait for the current serial native queue; no host submission.
while not (E/'NIV_K037/receipt.json').exists():
 s=(E/'NIV_OWNED_REPAIR_QUEUE.log').read_text()
 if 'STOP_NATIVE_PACKET' in s:sys.exit('prior native queue stopped; inspect before new launch')
 time.sleep(10)
for a,m in [('NIV_L005','NIV_OwnedPrefixes'),('NIV_L006','NIV_SnapshotDomain')]:
 r=subprocess.run([sys.executable,str(E/'NIV_formal.py'),a,'lean',m])
 if r.returncode:sys.exit(r.returncode)
sys.exit(subprocess.run([sys.executable,str(E/'NIV_packet_queue.py'),'sdk']).returncode)
