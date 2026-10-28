from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
names=[('NCP_digest','decode_contract'),('NCP_digest','decode_negative'),('NCP_digest','decode_caller'),('NCP_digest','decode_caller_negative'),('NCP_loops','for_invariant'),('NCP_loops','for_invariant_negative'),('NCP_loops','while_invariant'),('NCP_loops','while_invariant_negative'),('NCP_loops','while_bad_step'),('NCP_loops','while_weak')]
for i,(module,n) in enumerate(names,28):
 r=subprocess.run(['python3',str(E/'NCP_run.py'),f'NCP_K{i:03}',module+'::NCP_'+n],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 print(i,n,r.returncode,r.stdout[-2400:],flush=True)
 if 'STOP' in r.stdout or 'Traceback' in r.stdout:break
