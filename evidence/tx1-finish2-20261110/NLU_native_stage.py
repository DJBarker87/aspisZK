from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
names=['root_word','construct_owner','construct_claims','construct_alpha','construct_extra','construct_roots','construct_transcript','terminal_guard','circle_guard','arithmetic_arguments']
for k,name in enumerate(names):
 for bad,suffix in [(False,'cut'),(True,'control')]:
  n=5+2*k+int(bad);a=f'NLU_K{n:03}'
  if (E/a/'receipt.json').exists():continue
  subprocess.run([sys.executable,str(E/'NLU_kconfig.py'),a,'NLU_program::'+name+'_'+suffix],check=True)
  status=subprocess.run([sys.executable,str(E/'NLU_run.py'),a]).returncode
  log=(E/a/'stdout.log').read_text() if (E/a/'stdout.log').exists() else ''
  gp=E/(a+'-graph-check.json');lp=E/(a+'-lock-check.json');sp=E/(a+'-source-check.json');bp=E/(a+'-baseline-check.json')
  assert gp.exists() and json.loads(gp.read_text()).get('graph_matches_frozen') is True,'STOP graph validation'
  assert lp.exists() and json.loads(lp.read_text()).get('unchanged') is True,'STOP missing/drifted post-lock; recover read-only'
  assert sp.exists() and not json.loads(sp.read_text()).get('errors'),'STOP source drift'
  assert bp.exists() and not json.loads(bp.read_text()).get('errors'),'STOP frozen baseline drift'

  good=(status==1 and 'assertion failed: !selected' in log and 'VERIFICATION:- FAILED' in log) if bad else (status==0 and 'VERIFICATION:- SUCCESSFUL' in log)
  if not good:
   with (E/'NLU_NATIVE_FINDINGS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,exit=status,reason='No eligible paired credit; record and continue independent member; no rerun'))+'\n')
   print('Finding '+a+'; continue independent member',flush=True)
a='NLU_K025'
if (E/a/'receipt.json').exists():sys.exit(0)
subprocess.run([sys.executable,str(E/'NLU_kconfig.py'),a,'NLU_program::constructor_family_codegen','codegen'],check=True)
sys.exit(subprocess.run([sys.executable,str(E/'NLU_run.py'),a]).returncode)
