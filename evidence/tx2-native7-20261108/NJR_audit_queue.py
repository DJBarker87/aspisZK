"""One scope at a time; stop on any failed gate, never auto-resubmit."""
from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for attempt,kind,target in [('NJR_L049','lean','NJR_ProofDriver'),('NJR_L050','link','NJR_ProofDriver'),('NJR_L051','audit','fixtures'),('NJR_L052','audit','all'),('NJR_L053','lean','NJR_Driver'),('NJR_L054','link','NJR_Driver'),('NJR_L055','audit','scan')]:
 r=subprocess.run([sys.executable,str(E/'NJR_run.py'),attempt,kind,target])
 if r.returncode:sys.exit(r.returncode)
