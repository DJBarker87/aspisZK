from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for n,target,inv in [(4,'write_shape',True),(5,'write_value',False),(6,'write_value',True),(7,'write_frame',False),(8,'write_frame',True)]:
 env=dict(os.environ,NHX_CORE='1')
 if inv:env['NHX_INVERT']='1'
 r=subprocess.run(['python3',str(E/'NHX_run.py'),f'NHX_K{n:03}','kani','NHX_filled::'+target],env=env)
 log=(E/f'NHX_K{n:03}/stdout.log').read_text()
 if ('VERIFICATION:- FAILED' if inv else 'VERIFICATION:- SUCCESSFUL') not in log or 'timed out'in log.lower() or 'unwinding failures'in log:raise SystemExit(f'nonqualifying {n}')
