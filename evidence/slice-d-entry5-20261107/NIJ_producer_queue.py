from pathlib import Path
import subprocess,sys,json,lzma,time
E=Path(__file__).resolve().parent
while not (E/'NIJ_K055/receipt.json').exists():time.sleep(10)
for k,n in [(56,'producer_check'),(57,'producer_wrong')]:
 a=f'NIJ_K{k:03}';r=subprocess.run([sys.executable,str(E/'NIJ_run.py'),a,'kani','statement:pool_v1::verifier_registry::NIJ_registry::'+n],capture_output=True,text=True)
 p=E/a/'receipt.json'
 if not p.exists():print(r.stdout+r.stderr);sys.exit(1)
 x=json.loads(p.read_text());print(a,n,x['exit_status'],x['wall_seconds'],flush=True)
 s=lzma.decompress((p.parent/'stdout.log.xz').read_bytes()).decode()
 good=x['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in s if k==56 else x['exit_status']==1 and 'VERIFICATION:- FAILED' in s and '** 1 of ' in s and 'assertion' in s and 'unwinding' not in s and 'timed out' not in s
 if not good:print(r.stdout[-2500:]);sys.exit(1)
