from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
x=json.loads((E/'NHC_PROVENANCE.json').read_text())
for i,n in enumerate(x['order'][1:]+['COMBINED_IMPORT'],2):
 target='NHC_'+n
 a=f'NHC_L{i:03}'
 r=subprocess.run([sys.executable,str(E/'NHC_run.py'),a,'lean',target],capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 print(a,target,r.returncode,flush=True)
 if r.returncode:print((r.stdout+r.stderr)[-2200:]);sys.exit(r.returncode)
