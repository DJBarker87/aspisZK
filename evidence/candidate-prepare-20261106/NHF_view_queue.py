from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
for i,name,flag in [(20,'wide_copy',None),(21,'wide_copy','NHF_INVERT'),(22,'wide_view_result',None),(23,'wide_view_result','NHF_BAD_DECODE_ARG'),(24,'wide_view_result','NHF_BAD_REPLY')]:
 a=f'NHF_K{i:03d}';env=dict(os.environ)
 if flag:env[flag]='1'
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NHF_run.py'),a,'kani','verifier::candidate::NHF_wide::'+name],env=env,stdout=f,stderr=subprocess.STDOUT)
 raw=(E/a/'stdout.log').read_text() if (E/a/'stdout.log').exists() else ''
 good=('VERIFICATION:- FAILED' in raw and 'Failed Checks: assertion failed' in raw) if flag else 'VERIFICATION:- SUCCESSFUL' in raw
 print(json.dumps(dict(attempt=a,exit=r.returncode,expected_verdict=good)),flush=True)
 if not good or 'timed out' in raw.lower():raise SystemExit('STOP native view family')
