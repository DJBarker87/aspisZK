from pathlib import Path
import subprocess,sys
b=Path(__file__).resolve().parent
for mode in ['fixtures','final']:
 r=subprocess.run([str(b/'NFO_native/NFR_Driver'),mode],cwd=b)
 if r.returncode:sys.exit(r.returncode)
