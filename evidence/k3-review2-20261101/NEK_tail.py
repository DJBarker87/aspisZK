"""Remaining independent priority gates, each with distinct source/shape scope."""
import subprocess,sys
from pathlib import Path
E=Path(__file__).resolve().parent
for script,args in [('NEK_nibble_copy.py',[]),('NEK_ndn_matrix.py',[]),('NEK_nbp_forward.py',[]),('NEK_decoder_fidelity.py',['after','313']),('NEK_remaining_controls.py',[]),('NEK_cfg_copy.py',[]),('NEK_nbp_forward.py',['342'])]:
 with (E/(script.removesuffix('.py')+'.log')).open('a') as f:r=subprocess.run([sys.executable,str(E/script)]+args,stdout=f,stderr=subprocess.STDOUT)
 if r.returncode:raise SystemExit(script+' stopped; inspect own input or infrastructure before continuing')
