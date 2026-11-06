from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [(38,'NKK_RawSynchrony'),(39,'NKK_RawLength'),(41,'NKK_EmbedRaw'),(43,'NKK_DigestCut'),(46,'NKK_LogAlgebra'),(47,'NKK_ClauseRoot'),(49,'NKK_Compare')]:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_L{a:03}','lean',t])
 if r.returncode:break
