from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for i in range(33):
 a=f'NGK_L{78+i:03}';target=f'NGK_Statements{i:02}'
 r=subprocess.run([sys.executable,str(E/'NGK_run.py'),a,'lean',target],capture_output=True,text=True);(E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 print(a,target,'exit',r.returncode,flush=True)
 if r.returncode:print((r.stdout+r.stderr)[-3500:],flush=True);sys.exit(r.returncode)
