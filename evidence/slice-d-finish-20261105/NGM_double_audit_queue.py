from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
for a,kind,target in [('NGM_L054','lean','NGM_COMBINED_IMPORT'),('NGM_L055','auditbin','proof1'),('NGM_L056','auditbin','scan')]:
 r=subprocess.run([sys.executable,str(E/'NGM_run.py'),a,kind,target],capture_output=True,text=True);(E/(a+'-queue.log')).write_text(r.stdout+r.stderr);p=E/a/'receipt.json'
 if not p.exists():raise SystemExit(r.stdout[-1500:]+r.stderr[-1000:])
 x=json.loads(p.read_text());print(json.dumps({k:x[k]for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib']}),flush=True)
 if x['exit_status']:raise SystemExit(r.stdout[-2000:]+r.stderr[-1000:])
