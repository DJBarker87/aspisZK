"""Serial job-owned driver. Each child freshly checks admission and frozen graph."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
stages=[
 ('NBG_K007','crates/aspis-core','field::NBG_runtime::NBG_cm_add_sub_double_r','NBG_field.patch'),
 ('NBG_K008','crates/aspis-core','field::NBG_runtime::NBG_qm_add_sub','NBG_field.patch'),
 ('NBG_K009','crates/aspis-core','field::NBG_runtime::NBG_m31_bytes','NBG_field.patch'),
 ('NBG_K010','crates/aspis-core','field::NBG_runtime::NBG_cm_bytes','NBG_field.patch'),
 ('NBG_K011','crates/aspis-core','field::NBG_runtime::NBG_qm_bytes','NBG_field.patch'),
 ('NBG_K012','crates/aspis-core','field::NBG_runtime::NBG_constructors','NBG_field.patch'),
 ('NBG_K013','crates/aspis-r1-cost-probe','transport::NBG_runtime::NBG_transport','NBG_transport.patch'),
]
for a,c,h,p in stages:
 r=subprocess.run([sys.executable,str(E/'NBG_kani.py'),a,c,h,str(E/p)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout)
 print(a,'driver',r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
 # A failed proof is not replayed; its independent successors can proceed.
 rc=json.loads((E/a/'receipt.json').read_text());print('result',rc['exit_status'],flush=True)
