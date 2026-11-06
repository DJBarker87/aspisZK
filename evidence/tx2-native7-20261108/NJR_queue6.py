from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for n,name,flag in [(52,'query_raw','INVERT'),(53,'query_scalars','INVERT'),(54,'flush_receiver_window','INVERT'),(55,'flush_receiver_window','BAD_RECEIVER')]:
 env=os.environ.copy();env['NJR_'+flag]='1';a=f'NJR_K{n:03d}'
 r=subprocess.run(['python3',str(E/'NJR_run.py'),a,'kani','verifier::NJR_parent::'+name],env=env)
 raw=(E/a/'stdout.log').read_text()
 if r.returncode!=1 or 'VERIFICATION:- FAILED' not in raw or 'timed out' in raw:raise RuntimeError((a,'not a matched semantic FAIL'))
