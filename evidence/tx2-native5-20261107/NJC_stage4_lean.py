from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,m in [('NJC_L044','NJC_FilledClause'),('NJC_L045','NJC_ResumeCalls')]:
 r=subprocess.run(['python3',str(E/'NJC_run.py'),a,'lean',m]);assert r.returncode==0,(a,m)
 print(a+' passed '+m,flush=True)
