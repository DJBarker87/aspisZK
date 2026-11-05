from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for a,m in [('NIV_L007','NIV_SnapshotDomain'),('NIV_L008','NIV_OwnedPrefixes')]:
 r=subprocess.run([sys.executable,str(E/'NIV_formal.py'),a,'lean',m])
 if r.returncode:sys.exit(r.returncode)
sys.exit(subprocess.run([sys.executable,str(E/'NIV_packet_queue.py'),'sdk']).returncode)
