from pathlib import Path
import subprocess,sys,json,lzma
E=Path(__file__).resolve().parent
jobs=[]
for l in ['parse','semantic','transcript','relation','merkle','query','checkpoint','allocation']:
 jobs.extend(['error_'+l,'error_'+l+'_wrong'])
 if l=='parse':jobs.append('error_parse_stability')
for k,n in enumerate(jobs,39):
 a=f'NIJ_K{k:03}';r=subprocess.run([sys.executable,str(E/'NIJ_run.py'),a,'kani','NIJ_error::'+n],capture_output=True,text=True)
 p=E/a/'receipt.json'
 if not p.exists():print(r.stdout+r.stderr);sys.exit(1)
 x=json.loads(p.read_text());print(a,n,x['exit_status'],x['wall_seconds'],flush=True)
 s=lzma.decompress((p.parent/'stdout.log.xz').read_bytes()).decode()
 good=x['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in s if '_wrong' not in n else x['exit_status']==1 and 'VERIFICATION:- FAILED' in s and '** 1 of ' in s and 'assertion' in s and 'unwinding' not in s and 'timed out' not in s
 if not good:print(r.stdout[-2500:]);sys.exit(1)
