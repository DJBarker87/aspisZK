from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for number,mode in [(17,'positive'),(18,'frame-negative'),(19,'stability'),(20,'reply-negative')]:
 a=f'NIZ_K{number:03d}'
 subprocess.run([sys.executable,str(E/'NIZ_noop_prepare.py'),mode],check=True)
 shape=json.loads((E/'NIZ_CURRENT.json').read_text())
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NIZ_kani_run.py'),a,shape['harness']],stdout=f,stderr=subprocess.STDOUT)
 p=E/a/'receipt.json';assert p.exists(),'Missing receipt; recover read-only'
 d=json.loads(p.read_text());s=(E/a/'stdout.log').read_text();expected=1 if 'negative' in mode else 0
 check='result.is_ok()' if mode=='reply-negative' else 'observer == before'
 assert r.returncode==d['exit_status']==expected and 'timed out' not in s and ('Failed Checks: assertion failed: '+check if expected else 'VERIFICATION:- SUCCESSFUL') in s,a+' unexpected verdict'
 print(a+' '+mode+' '+('FAIL' if expected else 'PASS'),flush=True)
