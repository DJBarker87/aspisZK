from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for name in ['tail_mask_index','mask_dedup','mask_sort_swap','static_slot_guard','zero_weight_overwrite','guard_no_early_exit']:
 r=subprocess.run([sys.executable,str(E/'kani.py'),name],capture_output=True,text=True)
 print(r.stdout[-2000:]+r.stderr,flush=True)
 if r.returncode:sys.exit(r.returncode)
