from pathlib import Path
import subprocess,json,os
E=Path(__file__).resolve().parent
for i,t,control,expected in [(92,'KMX_checks::KMX_ptr_wrong',False,1),(93,'KMX_checks::KMX_slice_wrong',False,1),(94,'clone_cell',False,0),(95,'clone_cell',True,1)]:
 env=dict(os.environ,NIG_CORE='1')
 if control:env.update(NIG_INVERT='1',NIG_NATIVE_CFG='NIG_corrupt')
 a=f'NIG_K{i:03}';r=subprocess.run(['python3',str(E/'NIG_run.py'),a,'kani','NIG_filled::'+t],env=env)
 log=(E/a/'stdout.log').read_text()
 assert r.returncode==expected and'timed out'not in log.lower()and'unwinding failures'not in log,a
 assert ('VERIFICATION:- SUCCESSFUL'if expected==0 else'VERIFICATION:- FAILED')in log,a
