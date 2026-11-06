from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [(40,'NKK_RawAssociation'),(35,'NKK_CloseTail'),(36,'NKK_ClausesRun'),(37,'NKK_RawSlots'),(38,'NKK_RawSynchrony'),(39,'NKK_RawLength'),(41,'NKK_EmbedRaw'),(42,'NKK_RawPrefix'),(43,'NKK_DigestCut')]:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_L{a:03}','lean',t])
 if r.returncode:break
