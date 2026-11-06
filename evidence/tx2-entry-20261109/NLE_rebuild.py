from pathlib import Path
import subprocess,json,sys,hashlib
E=Path(__file__).resolve().parent
jobs=['NLE_OwnedFold','NLE_OwnedSource','NLE_OwnedValidate','NLE_OwnedProof','NLE_OwnedCheckpoint','NLE_OwnedEncode','NLE_OwnedEmit','NLE_OwnedTx2','NLE_OwnedFine','NLE_MapError','NLE_WrapperState','NLE_WrapperFold','NLE_WrapperSource','NLE_WrapperSteps','NLE_AuthLiteral']
start=int(sys.argv[1]) if len(sys.argv)>1 else 0
for i,module in enumerate(jobs):
 if i<start:continue
 a='NLE_L'+str(41+i).zfill(3)
 assert not (E/a).exists(), 'Never replay an existing attempt'
 r=subprocess.run([sys.executable,str(E/'NLE_run.py'),a,'lean',module])
 if r.returncode:sys.exit(r.returncode)
