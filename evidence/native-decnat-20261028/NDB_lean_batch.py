from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
start=int(sys.argv[1])
for target in sys.argv[2:]:
 a='NDB_L'+str(start).zfill(3);print('SELECT',a,target,flush=True)
 r=subprocess.run([sys.executable,str(E/'NDB_run.py'),a,'lean',target]);assert r.returncode==0
 rc=json.loads((E/a/'receipt.json').read_text());assert rc['exit_status']==0,'REVIEW '+a
 start+=1
