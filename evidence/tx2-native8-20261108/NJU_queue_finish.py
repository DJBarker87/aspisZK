from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for number,module in [(66,'NJU_WeakFinishPairCertificate'),(67,'NJU_WeakFinishPort')]:
 p=subprocess.run([sys.executable,str(E/'NJU_run.py'),f'NJU_L{number:03d}','lean',module])
 if p.returncode:raise SystemExit('Inspect changed proof before retry')
