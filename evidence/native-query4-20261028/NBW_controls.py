from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,name in enumerate(['ptr_wrong','clone_wrong','extend_wrong','to_vec_wrong','growth_wrong','slice_correct','ptr_correct','clone_correct','extend_correct','to_vec_correct','growth_correct'],3):
 r=subprocess.run([sys.executable,str(E/'NBW_run.py'),f'NBW_K{i:03d}','verifier::candidate::NBW_native::KMX_checks::KMX_'+name])
 if r.returncode:raise SystemExit(r.returncode)
