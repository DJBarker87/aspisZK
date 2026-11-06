from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[(58,'tail_guard',None),(59,'tail_guard','NJJ_INVERT'),(60,'prepared_tail',None),(61,'prepared_tail','NJJ_INVERT'),(62,'prepared_tail','NJJ_BAD_ALLOC'),(63,'accumulator_tail',None),(64,'accumulator_tail','NJJ_INVERT'),(65,'accumulator_tail','NJJ_BAD_ALLOC')]
for n,name,control in jobs:
 env=os.environ.copy()
 if control:env[control]='1'
 a=f'NJJ_K{n:03d}';r=subprocess.run(['python3',str(E/'NJJ_run.py'),a,'kani','verifier::NJJ_parent::'+name],env=env)
 assert (r.returncode==0)==(control is None),(a,r.returncode)
 log=(E/a/'stdout.log').read_text();assert 'timed out' not in log
 if control:assert 'VERIFICATION:- FAILED' in log
