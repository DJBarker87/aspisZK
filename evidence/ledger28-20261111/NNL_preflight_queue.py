from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,kind,target in [(5,'lean','NNL_Domains'),(6,'lean','NNL_COMBINED_IMPORT'),(7,'lean','NNL_Statements'),(8,'lean','NNL_Driver'),(9,'link','NNL_Driver'),(10,'audit','fixtures'),(11,'audit','scan')]:
 r=subprocess.run([sys.executable,str(E/'NNL_run.py'),f'NNL_L{i:03}',kind,target])
 if r.returncode:sys.exit(r.returncode)
