from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [(53,'NKK_ReadFrames'),(54,'NKK_DecoderDomain'),(55,'NKK_PrintOps'),(42,'NKK_RawPrefix'),(48,'NKK_QueryStage')]:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_L{a:03}','lean',t])
 if r.returncode:break
