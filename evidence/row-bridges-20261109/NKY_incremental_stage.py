from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
steps=[('NKY_L075','lean','NKY_BoxSource'),('NKY_L076','lean','NKY_COMBINED_IMPORT'),('NKY_L077','audit','scan'),('NKY_L078','audit','batch30'),('NKY_L079','audit','close'),('NKY_L080','audit','review-close')]
for a,k,t in steps:
 r=subprocess.run([sys.executable,str(E/'NKY_run.py'),a,k,t])
 if r.returncode:raise SystemExit(r.returncode)
 print(a,t,'complete',flush=True)
