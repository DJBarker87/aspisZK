from pathlib import Path
import subprocess,sys,shutil
E=Path(__file__).resolve().parent
jobs=[('lane','positive'),('lane','negative'),('digest','positive'),('digest','negative')]
for n,(slot,mode) in enumerate(jobs,137):
 a=f'NEX_K{n:03}'
 subprocess.run([sys.executable,str(E/'NEX_prepare_result_window.py'),slot,mode],check=True)
 shutil.copyfile(E/'NEX_RESULT_WINDOW_CURRENT.json',E/(a+'-WINDOW.json'))
 r=subprocess.run([sys.executable,str(E/'NEX_kani_run.py'),a,'kani','pool_v1::pair_forest_terminal::NEX_result_window::result_window'])
 if r.returncode != (0 if mode=='positive' else 1):raise SystemExit('unexpected runner exit '+str(r.returncode))
 print(a,slot,mode,flush=True)
