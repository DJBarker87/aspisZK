"""Final combined replay, justified only by NJR_WeightFailure source addition."""
from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for attempt,kind,target in [('NJR_L058','lean','NJR_COMBINED_IMPORT'),('NJR_L059','lean','NJR_ProofDriver'),('NJR_L060','link','NJR_ProofDriver'),('NJR_L061','audit','all'),('NJR_L062','audit','scan'),('NJR_L063','finalcheck','source-and-export'),('NJR_L064','cleanup','own-cargo-target-and-temp')]:
 r=subprocess.run([sys.executable,str(E/'NJR_run.py'),attempt,kind,target])
 if r.returncode:sys.exit(r.returncode)
