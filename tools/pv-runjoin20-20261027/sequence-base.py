from pathlib import Path
import subprocess,sys
R=Path(__file__).resolve().parents[2]
for a,m in [(37019,'PartsBlock20'),(37020,'SourceBlock0020'),(37021,'IndexedResultModel20')]:
 r=subprocess.run([sys.executable,str(R/'tools/pv-runjoin20-20261027/check.py'),str(a),'R1Z/PV_RunJoin_'+m],cwd=R)
 if r.returncode:sys.exit(r.returncode)
