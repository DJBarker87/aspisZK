from pathlib import Path
import subprocess,os
from NDN_verdicts import classify
E=Path(__file__).resolve().parent
for n,t,cfg in [(2,'state_only_poseidon::NDE_native::NDE_matrix_cell','NDE_matrix_step --cfg NDE_window_invert'),(3,'NDE_kmx::KMX_checks::KMX_ptr_correct',''),(4,'NDE_kmx::KMX_checks::KMX_ptr_wrong','')]:
 r=subprocess.run(['python3',str(E/'NDN_run.py'),f'NDN_K{n:03}','kani',t],env=dict(os.environ,NDN_RUST_CFG=cfg))
 if r.returncode:raise SystemExit(r.returncode)
 actual=classify((E/f"NDN_K{n:03}/stdout.log").read_text())
 expected="CHECK_FAILURE" if n in [2,4] else "PASS"
 assert actual==expected,(n,actual,expected)
