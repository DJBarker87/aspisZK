from pathlib import Path
import subprocess,os,sys
E=Path(__file__).resolve().parent
for a,fn,cfg in [('010','NEF_mark_frame','NEF_bad_mark'),('011','NEF_query_tail_frame',''),('012','NEF_query_tail_frame','NEF_bad_tail'),('013','NEF_inv_log',''),('014','NEF_inv_log','NEF_bad_inv')]:
 env=dict(os.environ,NEF_CFG=cfg)
 r=subprocess.run([sys.executable,str(E/'NEF_run.py'),'NEF_K'+a,'kani','verifier::candidate::NEF_native::'+fn],env=env);assert r.returncode==0
