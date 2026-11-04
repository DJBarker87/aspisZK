from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
for n in ['NGM_AddReference','NGM_ReferenceLinear','NGM_DoubleModel','NGM_DoubleProduct','NGM_ReferenceErrors','NGM_DotABI']:
 used=[int(p.parent.name[-3:])for p in E.glob('NGM_L*/receipt.json')];a=f'NGM_L{max(used)+1:03}'
 r=subprocess.run([sys.executable,str(E/'NGM_run.py'),a,'lean',n],capture_output=True,text=True);(E/(a+'-queue.log')).write_text(r.stdout+r.stderr);p=E/a/'receipt.json'
 if not p.exists():raise SystemExit(r.stdout[-1000:]+r.stderr[-1000:])
 x=json.loads(p.read_text());print(json.dumps({k:x[k]for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib']}),flush=True)
 if x['exit_status']:raise SystemExit(r.stdout[-2000:])
