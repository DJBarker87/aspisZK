from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,t in enumerate(['result_negative','result_weak_proof','result_real','result_unimplied','result_frame','slice_positive','slice_negative','slice_weak_proof','slice_real','slice_unimplied','slice_frame'],2):
 r=subprocess.run([sys.executable,str(E/'NCO_run.py'),f'NCO_K{i:03d}','kani','NCO_controls::'+t])
 if r.returncode:raise SystemExit(r.returncode)
