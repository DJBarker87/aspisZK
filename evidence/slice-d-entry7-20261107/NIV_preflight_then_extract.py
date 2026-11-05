from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for script in ['NIV_extract_preflight.py','NIV_extract.py']:
 r=subprocess.run([sys.executable,str(E/script)])
 if r.returncode:sys.exit(r.returncode)
