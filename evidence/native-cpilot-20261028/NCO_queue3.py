from pathlib import Path
import subprocess,sys,os,json
E=Path(__file__).resolve().parent
rows=[('NCO_L010','lean','NCO_Domains',None),('NCO_E005','extract','parser_references','parser')]
for a,k,t,cfg in rows:
 env=dict(os.environ)
 if cfg=='parser':env['NCO_EXTRACT_PARSER']='1'
 r=subprocess.run([sys.executable,str(E/'NCO_run.py'),a,k,t],env=env)
 if r.returncode:raise SystemExit(r.returncode)
