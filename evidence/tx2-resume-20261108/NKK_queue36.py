from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [(93,'NKK_RawCps'),(94,'NKK_DigestChain'),(95,'NKK_AllocationBind'),(96,'NKK_RootStatements')]:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_L{a:03}','lean',t])
 if r.returncode:break
