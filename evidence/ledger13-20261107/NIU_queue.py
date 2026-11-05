from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for a,k,t in [('NIU_L004','lean','NIU_Driver'),('NIU_L005','lean','NIU_ProofDriver'),('NIU_L006','link','NIU_Driver'),('NIU_L007','link','NIU_ProofDriver'),('NIU_L008','audit','scan'),('NIU_L009','audit','fixtures')]:
 r=subprocess.run([sys.executable,str(E/'NIU_run.py'),a,k,t])
 if r.returncode:sys.exit(r.returncode)
