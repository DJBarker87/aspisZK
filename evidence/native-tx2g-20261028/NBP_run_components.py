from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
names=['NBP_error::NBP_message_Parse']
for v in ['Semantic','Transcript','Relation','Merkle','Query','Checkpoint','Allocation']:
 names += ['NBP_error::NBP_debug_'+v,'NBP_error::NBP_message_'+v]
r=subprocess.run([sys.executable,str(E/'NBP_kaniserial.py'),'3','programs/r1-cost-probe',str(E/'NBP_components.patch'),*names])
raise SystemExit(r.returncode)
