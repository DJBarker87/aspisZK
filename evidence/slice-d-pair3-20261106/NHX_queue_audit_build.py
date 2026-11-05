from pathlib import Path
import subprocess,os,json,hashlib
E=Path(__file__).resolve().parent
for n,kind,target in [(12,'lean','NHX_COMBINED_IMPORT'),(13,'lean','NHX_Driver'),(14,'lean','NHX_ProofDriver'),(15,'linkaudit','NHX_Driver'),(16,'linkaudit','NHX_ProofDriver')]:
 r=subprocess.run(['python3',str(E/'NHX_run.py'),f'NHX_L{n:03}',kind,target]);assert r.returncode==0,(n,target)
r=subprocess.run(['python3',str(E/'NHX_run.py'),'NHX_L017','auditbin','fixtures'],env=dict(os.environ,NHX_AUDIT='1'));assert r.returncode==0
