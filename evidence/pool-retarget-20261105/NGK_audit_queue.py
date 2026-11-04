from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(52,'lean','NGK_Driver'),(53,'lean','NGK_ProofDriver'),(54,'link','NGK_Driver'),(55,'link','NGK_ProofDriver'),(56,'audit','fixtures'),(57,'audit','scan')]
groups=json.loads((E/'NGK_AUDIT_ROOTS.json').read_text())['groups'];jobs += [(58+i,'audit','batch'+str(i)) for i in range(len(groups))]
for i,kind,target in jobs:
 a=f'NGK_L{i:03}'
 r=subprocess.run([sys.executable,str(E/'NGK_run.py'),a,kind,target],capture_output=True,text=True);(E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 print(a,kind,target,'exit',r.returncode,flush=True)
 if r.returncode:print((r.stdout+r.stderr)[-4500:],flush=True);sys.exit(r.returncode)
