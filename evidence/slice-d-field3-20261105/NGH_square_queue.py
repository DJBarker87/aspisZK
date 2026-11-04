from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
jobs=[('NGH_K012','kani','field::NGH_qsquare::square_log',{'NGH_CORE':'1','NGH_INVERT':'1'}),('NGH_K013','kani','field::NGH_qsquare::square_log',{'NGH_CORE':'1','NGH_BADARG':'1'}),('NGH_K014','kani','field::NGH_qsquare::copy_positive',{'NGH_CORE':'1'}),('NGH_K015','kani','field::NGH_qsquare::copy_negative',{'NGH_CORE':'1'}),('NGH_L004','lean','NGH_Inspect',{}),('NGH_L005','lean','NGH_QSquareRef',{}),('NGH_L006','lean','NGH_SmallValue',{})]
for a,kind,h,extra in jobs:
 r=subprocess.run(['python3',str(E/'NGH_run.py'),a,kind,h],env=dict(os.environ,**extra),capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr);p=E/a/'receipt.json'
 if not p.exists():raise RuntimeError(r.stdout+r.stderr)
 x=json.loads(p.read_text());print(a,h,x['exit_status'],x['wall_seconds'],flush=True)
 if kind=='kani' and a in ['NGH_K014'] and x['exit_status']!=0:raise RuntimeError('Positive failed; inspect before proceeding')
