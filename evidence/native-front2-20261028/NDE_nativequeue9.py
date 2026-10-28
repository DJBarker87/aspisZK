from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for n,t,mode in [(50,'NDE_matrix_cell','NDE_matrix_step'),(52,'NDE_scan_cell','NDE_scan_step'),(54,'NDE_packed_after','NDE_packed_after')]:
 for neg in range(2):
  cfg=mode+(' --cfg NDE_invert' if neg else '')
  r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_K{n+neg:03}','kani','state_only_poseidon::NDE_native::'+t],env=dict(os.environ,NDE_RUST_CFG=cfg))
  if r.returncode:raise SystemExit(r.returncode)
