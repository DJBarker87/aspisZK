from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
# Finish the repaired source ? dispatch family, then callback/planner CFG cuts.
subprocess.run([sys.executable,str(E/'NIZ_domain_prepare.py'),'questionmark','negative'],check=True)
a='NIZ_K029'
with (E/(a+'-client.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NIZ_kani_run.py'),a,'processor::NIZ_native::certificate'],stdout=f,stderr=subprocess.STDOUT)
p=E/a/'receipt.json';assert p.exists(),'Missing receipt; recover read-only'
s=(E/a/'stdout.log').read_text();assert r.returncode==1 and 'Failed Checks: assertion failed: seen == ok' in s and 'timed out' not in s,a
print(a+' questionmark semantic control FAIL',flush=True)
for index,label in enumerate(['forest_planner','callback_deposit','callback_prevalidated_deposit','callback_withdrawal']):
 for delta,mode in [(0,'positive'),(1,'negative')]:
  a=f'NIZ_K{30+index*2+delta:03d}'
  subprocess.run([sys.executable,str(E/'NIZ_cfg_prepare.py'),label,mode],check=True)
  with (E/(a+'-client.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NIZ_kani_run.py'),a,'processor::NIZ_native::certificate'],stdout=f,stderr=subprocess.STDOUT)
  p=E/a/'receipt.json';assert p.exists(),'Missing receipt; recover read-only'
  d=json.loads(p.read_text());raw=(E/a/'stdout.log').read_text();expected=0 if mode=='positive' else 1
  assert r.returncode==d['exit_status']==expected and 'timed out' not in raw and ('VERIFICATION:- SUCCESSFUL' if mode=='positive' else 'Failed Checks: assertion failed: !safe_source || barrier || safe_target') in raw,a+' unexpected verdict'
  print(a+' '+label+' '+('PASS' if mode=='positive' else 'semantic control FAIL'),flush=True)
