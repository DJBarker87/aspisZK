from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,name in enumerate(['NBW_NBB_add_frame','NBW_NBB_fold_frame','NBW_compare_eight_coordinates','NBW_capacity_finish_window','NBW_initializer_window'],46):
 r=subprocess.run([sys.executable,str(E/'NBW_run.py'),f'NBW_K{i:03d}',name])
 if r.returncode:raise SystemExit(r.returncode)
