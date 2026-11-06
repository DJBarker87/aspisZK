from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
jobs=[(28,'lean','NJJ_COMBINED_IMPORT'),(29,'lean','NJJ_ProofDriver'),(30,'link','NJJ_ProofDriver'),(31,'audit','fixtures'),(32,'audit','all'),(33,'lean','NJJ_Driver'),(34,'link','NJJ_Driver'),(35,'audit','scan'),(36,'finalcheck','finalcheck'),(37,'cleanup','cleanup')]
for n,kind,target in jobs:
 r=subprocess.run(['python3',str(E/'NJJ_run.py'),f'NJJ_L{n:03d}',kind,target]);assert r.returncode==0,(n,kind,target,r.returncode)
