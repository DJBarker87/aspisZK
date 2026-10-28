from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
jobs=[(43,'NCP_scalar::NCP_canon_negative'),(44,'NCP_scalar::NCP_canon_caller'),(45,'NCP_scalar::NCP_canon_caller_negative')]
for start,width in [(46,8),(50,32)]:
 for j,kind in enumerate(['contract','negative','caller','caller_negative']):jobs.append((start+j,f'pool_v1::pair_terminal::NCP_after::NCP_exact{width}_{kind}'))
for j,kind in enumerate(['contract','negative','caller','caller_negative']):jobs.append((54+j,'pool_v1::pair_terminal::NCP_after::NCP_after_'+kind))
blocked=set()
for i,n in jobs:
 group=n.rsplit('_',1)[0] if 'exact' in n else 'after' if 'NCP_after_' in n else 'canon'
 if any(t in n for t in blocked):print(i,n,'SKIP: earlier timeout in same member',flush=True);continue
 r=subprocess.run(['python3',str(E/'NCP_run.py'),f'NCP_K{i:03}',n],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 print(i,n,r.returncode,r.stdout[-3000:],flush=True)
 if 'STOP' in r.stdout or 'Traceback' in r.stdout:break
 log=(E/f'NCP_K{i:03}'/'stdout.log').read_text()
 if 'Timed out' in log or 'TIMEOUT' in log:
  blocked.add('NCP_exact8' if 'NCP_exact8' in n else 'NCP_exact32' if 'NCP_exact32' in n else 'NCP_after_' if 'NCP_after_' in n else 'NCP_canon')
