from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
jobs=[('NGM_L017','lean','NGM_FinishControl'),('NGM_L018','lean','NGM_COMBINED_IMPORT'),('NGM_L019','lean','NGM_Driver'),('NGM_L020','lean','NGM_ProofDriver'),('NGM_L021','auditbatch','NGM_ProofDriver')]
for a,kind,target in jobs:
 r=subprocess.run([sys.executable,str(E/'NGM_run.py'),a,kind,target],capture_output=True,text=True)
 (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json'
 if not p.exists():raise SystemExit('Missing receipt: '+r.stdout[-1000:]+r.stderr[-1000:])
 x=json.loads(p.read_text());print(json.dumps({k:x[k]for k in ['attempt','exit_status','wall_seconds','peak_rss_kib']}),flush=True)
 if x['exit_status']:raise SystemExit(r.stdout[-2000:]+r.stderr[-1000:])
