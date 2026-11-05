from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for i,kind in enumerate(['keyview','prefix','groups','questionmark']):
 for j,mode in enumerate(['positive','negative']):
  a=f'NIZ_K{21+2*i+j:03d}'
  subprocess.run([sys.executable,str(E/'NIZ_domain_prepare.py'),kind,mode],check=True)
  shape=json.loads((E/'NIZ_CURRENT.json').read_text());module={'keyview':'processor','questionmark':'processor','prefix':'pair_processor','groups':'deposit'}[kind]
  with (E/(a+'-client.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NIZ_kani_run.py'),a,module+'::NIZ_native::certificate'],stdout=f,stderr=subprocess.STDOUT)
  p=E/a/'receipt.json';assert p.exists(),'Missing receipt; recover read-only'
  d=json.loads(p.read_text());s=(E/a/'stdout.log').read_text();expected=0 if mode=='positive' else 1
  assert r.returncode==d['exit_status']==expected and 'timed out' not in s and ('VERIFICATION:- SUCCESSFUL' if not expected else 'Failed Checks: assertion failed:') in s,a+' unexpected verdict'
  print(a+' '+kind+' '+('PASS' if not expected else 'semantic FAIL'),flush=True)
