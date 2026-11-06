from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[(12,'flush_receiver_window',None),(13,'flush_receiver_window','BAD_RECEIVER'),(14,'flush_receiver_window','INVERT'),(15,'flush_destination_window',None),(16,'flush_destination_window','BAD_DESTINATION'),(17,'flush_destination_window','INVERT'),(18,'query_weights',None),(19,'query_weights','INVERT'),(20,'query_raw',None),(21,'query_raw','INVERT'),(22,'query_scalars',None),(23,'query_scalars','INVERT')]
for number,name,control in jobs:
 env=os.environ.copy()
 if control:env['NJR_'+control]='1'
 a=f'NJR_K{number:03d}';r=subprocess.run(['python3',str(E/'NJR_run.py'),a,'kani','verifier::NJR_parent::'+name],env=env)
 raw=(E/a/'stdout.log').read_text()
 if 'timed out' in raw or 'Timed out' in raw:raise RuntimeError((a,'timeout; isolate'))
 if (r.returncode==0)!=(control is None):raise RuntimeError((a,r.returncode))
 if control and 'VERIFICATION:- FAILED' not in raw:raise RuntimeError((a,'not a semantic control'))
