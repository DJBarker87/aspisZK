from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[(30,'query_raw',None),(31,'query_raw','BAD_QUERY_RAW_OWNER'),(32,'query_scalars',None),(33,'query_scalars','BAD_POWER'),(34,'query_scalars','BAD_NEXT'),(35,'query_scalars','BAD_TERMS'),(36,'query_scalars','BAD_ERROR'),(37,'flush_receiver_window',None),(38,'flush_receiver_window','BAD_RECEIVER_POINTER'),(39,'pending_destination',None),(40,'pending_destination','BAD_DESTINATION'),(41,'pending_destination','INVERT')]
for number,name,control in jobs:
 env=os.environ.copy()
 if control:env['NJR_'+control]='1'
 a=f'NJR_K{number:03d}';r=subprocess.run(['python3',str(E/'NJR_run.py'),a,'kani','verifier::NJR_parent::'+name],env=env)
 raw=(E/a/'stdout.log').read_text()
 if 'timed out' in raw or 'Timed out' in raw:raise RuntimeError((a,'timeout; isolate'))
 if (r.returncode==0)!=(control is None):raise RuntimeError((a,r.returncode))
 if control and 'VERIFICATION:- FAILED' not in raw:raise RuntimeError((a,'not a semantic control'))
