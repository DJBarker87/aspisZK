from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,k,t in [(97,'lean','NKK_COMBINED_IMPORT'),(98,'lean','NKK_ProofDriver'),(99,'lean','NKK_Driver'),(100,'link','NKK_ProofDriver'),(11,'link','NKK_Driver'),(12,'audit','all'),(13,'audit','scan'),(14,'audit','fixtures')]:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_L{a:03}',k,t])
 if r.returncode:break
