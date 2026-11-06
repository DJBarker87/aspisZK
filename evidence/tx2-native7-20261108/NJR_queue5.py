from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
# The shared harness source changed after the first Reader/weights/destination
# passes (new source cuts and corrected SAME-store destination). These focused
# final-snapshot checks bind the selected certificates to one exact source hash.
jobs=[(42,'reader_backing',None),(43,'reader_backing','BAD_BACKING'),(44,'reader_backing','BAD_DROP'),(45,'reader_backing','INVERT'),(46,'query_weights',None),(47,'query_weights','INVERT'),(48,'query_weights','BAD_QUERY_WEIGHT_OWNER'),(49,'flush_destination_window',None),(50,'flush_destination_window','BAD_DESTINATION'),(51,'flush_destination_window','INVERT')]
for number,name,control in jobs:
 env=os.environ.copy()
 if control:env['NJR_'+control]='1'
 a=f'NJR_K{number:03d}';r=subprocess.run(['python3',str(E/'NJR_run.py'),a,'kani','verifier::NJR_parent::'+name],env=env)
 raw=(E/a/'stdout.log').read_text()
 if 'timed out' in raw or 'Timed out' in raw:raise RuntimeError((a,'timeout; isolate'))
 if (r.returncode==0)!=(control is None):raise RuntimeError((a,r.returncode))
 if control and 'VERIFICATION:- FAILED' not in raw:raise RuntimeError((a,'not a semantic control'))
