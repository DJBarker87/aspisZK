from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for i,t,control in [(116,'new_slot',True),(117,'pair_slot',False),(118,'pair_slot',True)]:
 env=dict(os.environ)
 if control:env.update(NIG_INVERT='1',NIG_NATIVE_CFG='NIG_corrupt')
 a=f'NIG_K{i:03}';r=subprocess.run(['python3',str(E/'NIG_run.py'),a,'kani','weights::NIG_stages::'+t],env=env)
 log=(E/a/'stdout.log').read_text();assert r.returncode==(1 if control else 0)and'timed out'not in log.lower()and'unwinding failures'not in log,a
 assert('VERIFICATION:- FAILED'if control else'VERIFICATION:- SUCCESSFUL')in log,a
