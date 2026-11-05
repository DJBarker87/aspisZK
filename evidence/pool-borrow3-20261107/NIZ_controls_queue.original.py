from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for number,mode in [(7,'negative'),(8,'frame-negative')]:
 a=f'NIZ_K{number:03d}'
 subprocess.run([sys.executable,str(E/'NIZ_memcmp_window_prepare.py'),mode],check=True)
 with (E/(a+'-client.log')).open('w') as f:
  r=subprocess.run([sys.executable,str(E/'NIZ_kani_run.py'),a,'processor::NIZ_native::certificate'],stdout=f,stderr=subprocess.STDOUT)
 p=E/a/'receipt.json'
 assert p.exists(),'Missing submitted receipt; read-only recovery required'
 d=json.loads(p.read_text());out=(E/a/'stdout.log').read_text()
 assert r.returncode==1 and d['exit_status']==1 and 'VERIFICATION:- FAILED' in out and '1 of 28 failed' in out and 'Failed Checks: assertion failed:' in out and 'timed out' not in out, a+' did not fail as the matched semantic control'
 print(a+' matched semantic control FAIL',flush=True)
