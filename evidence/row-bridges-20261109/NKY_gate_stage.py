from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
steps=[('NKY_L028','lean','NKY_COMBINED_IMPORT'),('NKY_L029','lean','NKY_Driver'),('NKY_L030','link','NKY_Driver'),('NKY_L031','lean','NKY_ProofDriver'),('NKY_L032','link','NKY_ProofDriver'),('NKY_L033','audit','fixtures'),('NKY_L034','audit','scan')]
for a,k,t in steps:
 r=subprocess.run([sys.executable,str(E/'NKY_run.py'),a,k,t])
 if r.returncode:raise SystemExit(r.returncode)
 print(a,t,'complete',flush=True)
