from pathlib import Path
import os,subprocess
E=Path(__file__).resolve().parent
for i,t,control in [(110,'same_guard_stage',True),(111,'initial_stage',False),(112,'initial_stage',True)]:
 env=dict(os.environ)
 if control:env.update(NIG_INVERT='1',NIG_NATIVE_CFG='NIG_corrupt')
 a=f'NIG_K{i:03}';r=subprocess.run(['python3',str(E/'NIG_run.py'),a,'kani','weights::NIG_stages::'+t],env=env)
 log=(E/a/'stdout.log').read_text();assert r.returncode==(1 if control else 0)and'timed out'not in log.lower()and'unwinding failures'not in log,a
 assert('VERIFICATION:- FAILED'if control else'VERIFICATION:- SUCCESSFUL')in log,a
