from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for a,family,mode in [('NHC_K118','forward','negative'),('NHC_K119','iterate','positive'),('NHC_K120','iterate','negative')]:
 subprocess.run([sys.executable,str(E/'NHC_dynamic_span.py'),family,mode],check=True,capture_output=True)
 r=subprocess.run([sys.executable,str(E/'NHC_kani_run.py'),a,'pair_forest::NHC_DynamicSpan::association'],capture_output=True,text=True);(E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 raw=(E/a/'stdout.log').read_text();good=('VERIFICATION:- SUCCESSFUL' in raw) if mode=='positive' else ('VERIFICATION:- FAILED' in raw and 'Failed Checks:' in raw)
 print(a,family,mode,r.returncode,'expected',good,flush=True)
 if not good:print('Review; no dependent resubmission');sys.exit(3)
