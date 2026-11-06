from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,k in [(17,'tools'),(18,'sourcecheck'),(19,'export'),(20,'verify'),(21,'retention')]:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_L{a:03}',k,'all'])
 if r.returncode:break
