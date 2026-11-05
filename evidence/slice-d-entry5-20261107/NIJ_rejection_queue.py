from pathlib import Path
import subprocess,sys,json,lzma
E=Path(__file__).resolve().parent
jobs=['lifecycle_4','lifecycle_4_wrong','lifecycle_5','lifecycle_5_wrong','lifecycle_6','lifecycle_6_wrong','other_rejected','other_rejected_wrong','stage2_no_accounts']
for k,n in enumerate(jobs,112):
 a=f'NIJ_K{k:03}';r=subprocess.run([sys.executable,str(E/'NIJ_run.py'),a,'kani','r1_pool_adapter::owned::NIJ_entry::'+n],capture_output=True,text=True)
 p=E/a/'receipt.json'
 if not p.exists():print(r.stdout+r.stderr);sys.exit(1)
 x=json.loads(p.read_text());print(a,n,x['exit_status'],x['wall_seconds'],flush=True)
 s=lzma.decompress((p.parent/'stdout.log.xz').read_bytes()).decode()
 good=x['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in s if '_wrong' not in n else x['exit_status']==1 and 'VERIFICATION:- FAILED' in s and '** 1 of ' in s and 'assertion' in s and 'unwinding' not in s and 'timed out' not in s
 if not good:print(r.stdout[-2500:]);sys.exit(1)
