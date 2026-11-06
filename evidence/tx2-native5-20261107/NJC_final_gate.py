from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
jobs=[(76,'lean','NJC_COMBINED_IMPORT'),(77,'lean','NJC_ProofDriver'),(78,'link','NJC_ProofDriver'),(79,'audit','fixtures')]
jobs += [(80+i,'audit','batch'+str(i)) for i in range(len(json.loads((E/'NJC_AUDIT_ROOTS.json').read_text())['groups']))]
jobs += [(85,'audit','scan'),(86,'finalcheck','finalcheck'),(87,'cleanup','cleanup')]
for n,kind,target in jobs:
 r=subprocess.run(['python3',str(E/'NJC_run.py'),f'NJC_L{n:03d}',kind,target]);assert r.returncode==0,(n,kind,target,r.returncode)
 print(f'NJC_L{n:03d} gate passed',flush=True)
