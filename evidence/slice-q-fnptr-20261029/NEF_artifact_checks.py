from pathlib import Path
import subprocess,os,sys
E=Path(__file__).resolve().parent
for a,fn,cfg in [('021','NEF_all_phases',''),('022','NEF_all_phases','NEF_bad_result'),('023','NEF_query_nonempty_tail',''),('024','NEF_query_nonempty_tail','NEF_bad_nonempty')]:
 r=subprocess.run([sys.executable,str(E/'NEF_run.py'),'NEF_K'+a,'kani','verifier::candidate::NEF_native::'+fn],env=dict(os.environ,NEF_CFG=cfg));assert r.returncode==0
