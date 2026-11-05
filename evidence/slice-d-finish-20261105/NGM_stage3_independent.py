from pathlib import Path
import subprocess,json,sys,shutil
E=Path(__file__).resolve().parent

def run(kind,target):
 used=[int(p.parent.name[-3:])for p in E.glob('NGM_L*/receipt.json')]
 a='NGM_E002'if kind=='extract'else f'NGM_L{max(used,default=0)+1:03}'
 r=subprocess.run([sys.executable,str(E/'NGM_run.py'),a,kind,target],capture_output=True,text=True)
 (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json'
 if not p.exists():raise SystemExit('Missing receipt: '+r.stdout[-1500:]+r.stderr[-1000:])
 x=json.loads(p.read_text());print(json.dumps({k:x[k]for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib']}),flush=True)
 return x['exit_status']==0
run('lean','NGM_ReferenceResult')
probe=run('lean','NGM_ProbeTransport')
if not run('extract','NGM_DoubleRef'):raise SystemExit('Double extraction blocked')
for n in ['Types','Funs']:
 p=E/'NGM_DoubleRef'/(n+'.lean');p.parent.mkdir(exist_ok=True);shutil.copyfile(E/'NGM_extracted/NGM_DoubleRef/NGM_DoubleRef'/(n+'.lean'),p)
for target in ['NGM_DoubleRef/Types','NGM_DoubleRef/Funs','NGM_ResultLaws','NGM_AddReference','NGM_ScalarCanon','NGM_ReferenceLinear','NGM_DoubleModel']:
 if not run('lean',target):raise SystemExit('Dependent Double item stopped; independent work remains')
if probe:run('lean','NGM_DoubleProduct')
