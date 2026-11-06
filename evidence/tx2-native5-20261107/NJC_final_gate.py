from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
jobs=[(90,'lean','NJC_COMBINED_IMPORT'),(91,'lean','NJC_ProofDriver'),(92,'link','NJC_ProofDriver'),(93,'audit','fixtures'),(94,'audit','all'),(95,'audit','scan'),(96,'finalcheck','finalcheck'),(97,'cleanup','cleanup')]
for n,kind,target in jobs:
 r=subprocess.run(['python3',str(E/'NJC_run.py'),f'NJC_L{n:03d}',kind,target]);assert r.returncode==0,(n,kind,target,r.returncode)
 print(f'NJC_L{n:03d} gate passed',flush=True)
