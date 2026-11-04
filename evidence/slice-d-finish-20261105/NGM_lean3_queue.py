from pathlib import Path
import subprocess,json,sys,shutil
E=Path(__file__).resolve().parent
jobs=[('NGM_L023','lean','NGM_AcceptDecision'),('NGM_L024','lean','NGM_FinishRef/Types'),('NGM_L025','lean','NGM_FinishRef/Funs'),('NGM_L026','lean','NGM_WordArrayEquality'),('NGM_L027','lean','NGM_ReferenceResult'),('NGM_L028','lean','NGM_ProbeTransport'),('NGM_E002','extract','NGM_DoubleRef')]
jobs += [(f'NGM_L{i:03}','lean',n)for i,n in enumerate(['NGM_DoubleRef/Types','NGM_DoubleRef/Funs','NGM_ResultLaws','NGM_AddReference','NGM_ScalarCanon','NGM_ReferenceLinear','NGM_DoubleModel','NGM_DoubleProduct'],29)]
for a,kind,target in jobs:
 if a=='NGM_L029':
  for n in ['Types','Funs']:
   p=E/'NGM_DoubleRef'/(n+'.lean');p.parent.mkdir(exist_ok=True);shutil.copyfile(E/'NGM_extracted/NGM_DoubleRef/NGM_DoubleRef'/(n+'.lean'),p)
 r=subprocess.run([sys.executable,str(E/'NGM_run.py'),a,kind,target],capture_output=True,text=True)
 (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json'
 if not p.exists():raise SystemExit('Missing receipt: '+r.stdout[-1000:]+r.stderr[-1000:])
 x=json.loads(p.read_text());print(json.dumps({k:x[k]for k in ['attempt','exit_status','wall_seconds','peak_rss_kib']}),flush=True)
 if x['exit_status']:raise SystemExit(r.stdout[-2000:]+r.stderr[-1000:])
