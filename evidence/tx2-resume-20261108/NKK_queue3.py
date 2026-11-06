from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [(22,'NKK_ClausesQueryMid'),(23,'NKK_ClausesQueryBlock'),(24,'NKK_ClausesResumeBody'),(25,'NKK_ClausesRun'),(26,'NKK_NativeRaw'),(27,'NKK_RawChain'),(28,'NKK_RawFold'),(29,'NKK_RawAssociation')]:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_L{a:03}','lean',t])
 if r.returncode:break
