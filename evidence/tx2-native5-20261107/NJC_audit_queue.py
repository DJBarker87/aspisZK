from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,kind,target in [('NJC_L024','lean','NJC_Driver'),('NJC_L025','lean','NJC_ProofDriver'),('NJC_L026','link','NJC_Driver'),('NJC_L027','link','NJC_ProofDriver'),('NJC_L028','audit','fixtures'),('NJC_L029','audit','batch0'),('NJC_L030','audit','batch1'),('NJC_L031','audit','scan')]:
 r=subprocess.run(['python3',str(E/'NJC_run.py'),a,kind,target]);assert r.returncode==0,(a,kind,target)
 print(a+' gate passed '+target,flush=True)
