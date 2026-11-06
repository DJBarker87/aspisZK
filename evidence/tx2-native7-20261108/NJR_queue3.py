from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[(26,'query_weights',None),(27,'query_weights','BAD_QUERY_WEIGHT_OWNER'),(28,'query_raw',None),(29,'query_raw','BAD_QUERY_RAW_OWNER'),(30,'query_scalars',None),(31,'query_scalars','BAD_POWER'),(32,'query_scalars','BAD_NEXT'),(33,'query_scalars','BAD_TERMS'),(34,'query_scalars','BAD_ERROR'),(35,'flush_receiver_window',None),(36,'flush_receiver_window','BAD_RECEIVER_POINTER')]
for number,name,control in jobs:
 env=os.environ.copy()
 if control:env['NJR_'+control]='1'
 a=f'NJR_K{number:03d}';r=subprocess.run(['python3',str(E/'NJR_run.py'),a,'kani','verifier::NJR_parent::'+name],env=env)
 raw=(E/a/'stdout.log').read_text()
 if 'timed out' in raw or 'Timed out' in raw:raise RuntimeError((a,'timeout; isolate'))
 if (r.returncode==0)!=(control is None):raise RuntimeError((a,r.returncode))
 if control and 'VERIFICATION:- FAILED' not in raw:raise RuntimeError((a,'not a semantic control'))
