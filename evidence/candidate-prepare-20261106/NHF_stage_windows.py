"""Independent native callee-output windows, each with a matched corruption."""
from pathlib import Path
import json,subprocess,os,sys
sys.dont_write_bytecode=True
from NHF_stage_generate import generate
E=Path(__file__).resolve().parent
jobs=[('row',r,30+2*r)for r in range(27)]+[('prefix',0,84),('values',0,86)]
for kind,row,first in jobs:
 spec=generate(kind,row)
 for bad in [False,True]:
  a=f'NHF_K{first+int(bad):03d}';env=dict(os.environ)
  if bad:env['NHF_BAD_STAGE']='1'
  target='verifier::candidate::NHF_stages::'+('values_stage' if kind=='values'else 'semantic_stage')
  with (E/(a+'-client.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NHF_run.py'),a,'kani',target],env=env,stdout=f,stderr=subprocess.STDOUT)
  raw=(E/a/'stdout.log').read_text() if (E/a/'stdout.log').exists() else ''
  expected=('VERIFICATION:- FAILED' in raw and 'Failed Checks: assertion failed' in raw) if bad else 'VERIFICATION:- SUCCESSFUL' in raw
  entry=dict(attempt=a,**spec,control=bad,exit=r.returncode,expected_verdict=expected)
  with (E/'NHF_STAGE_WINDOW_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
  print(json.dumps({k:entry[k] for k in ['attempt','kind','row','control','exit','expected_verdict']}),flush=True)
  if not expected or 'timed out' in raw.lower():raise SystemExit('STOP case; inspect/split before continuing')
