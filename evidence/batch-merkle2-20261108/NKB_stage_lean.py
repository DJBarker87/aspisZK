"""Independent focused modules, serial scopes, each distinct source compiled once."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for n,module in [(14,'NKB_CallerDomain'),(15,'NKB_CallerPrefix'),(16,'NKB_PaddingFrame'),(17,'NKB_PaddingPredicate'),(18,'NKB_ScanWindows'),(19,'NKB_SortProducer'),(20,'NKB_LeafChain'),(21,'NKB_Rejection'),(22,'NKB_StrictCount')]:
 r=subprocess.run([sys.executable,str(E/'NKB_compile.py'),str(n),module])
 if r.returncode:
  log=E/f'NKB_L{n:03d}'/'stdout.log'
  if log.exists():
   lines=[t for t in log.read_text().splitlines() if 'error:' in t or 'error(' in t];print(module+': '+(' | '.join(lines))[:900],flush=True)
print('NKB independent focused stage complete; inspect every result',flush=True)
